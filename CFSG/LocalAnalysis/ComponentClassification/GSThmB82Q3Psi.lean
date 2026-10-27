module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Q3T2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Q3F3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Q3GDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TLayer

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace Q3Psi

variable {X : Type} [Group X] [Finite X]

private theorem psi_kernel_of_sup {K L : Subgroup X} {g : X}
    (hKL : K ⊔ (pPrimeCore 2 ↥L).map L.subtype = L) (hgN : g ∈ normalizer (L : Set X))
    (hgK : ∀ k ∈ K, g * k = k * g) : g ∈ coreActionKernel L := by
  have hKL' : K ≤ L := le_sup_left.trans_eq hKL
  have hON : g ∈ normalizer (((pPrimeCore 2 ↥L).map L.subtype : Subgroup X) : Set X) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 ↥L) hgN
  have hKO : K ≤ normalizer (((pPrimeCore 2 ↥L).map L.subtype : Subgroup X) : Set X) :=
    fun k hk => UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 ↥L)
      (le_normalizer (hKL' hk))
  refine mem_coreActionKernel.mpr ⟨hgN, fun l hl => ?_⟩
  rw [← hKL] at hl
  obtain ⟨k, hk, o, ho, rfl⟩ := (UnbalancedGS.mem_sup_iff_exists_mul hKO).mp hl
  have h1 : g⁻¹ * o * g ∈ (pPrimeCore 2 ↥L).map L.subtype := by
    have h2 := (mem_normalizer_iff.mp (inv_mem hON) o).mp ho
    rwa [inv_inv] at h2
  have e : k⁻¹ * g⁻¹ * k = g⁻¹ := by
    rw [show k⁻¹ * g⁻¹ = (g * k)⁻¹ by group, hgK k hk]
    group
  have e2 : (k * o)⁻¹ * g⁻¹ * (k * o) * g = o⁻¹ * (g⁻¹ * o * g) := by
    calc (k * o)⁻¹ * g⁻¹ * (k * o) * g = o⁻¹ * (k⁻¹ * g⁻¹ * k) * o * g := by group
      _ = o⁻¹ * (g⁻¹ * o * g) := by rw [e]; group
  rw [e2]
  exact mul_mem (inv_mem ho) h1

private theorem psi_oddCore_le {K L : Subgroup X} (hKL : K ≤ L)
    (h : K ⊔ (pPrimeCore 2 ↥L).map L.subtype = L) :
    (pPrimeCore 2 ↥K).map K.subtype ≤ (pPrimeCore 2 ↥L).map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥K →* ↥L ⧸ pPrimeCore 2 ↥L :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥L)).comp (inclusion hKL) with hf
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, hf, MonoidHom.range_comp, inclusion_range]
    exact (UnbalancedGS.sup_primeCore_eq_iff_map_eq_top hKL).mp h
  have h2 := Semidihedral.OddCoreQuotient.pPrimeCore_map_le_of_surjective 2 f hsurj
  rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2] at h2
  rintro _ ⟨k, hk, rfl⟩
  have h3 : f k = 1 := by
    have h4 := h2 (mem_map_of_mem f hk)
    rwa [mem_bot] at h4
  have h4 : inclusion hKL k ∈ pPrimeCore 2 ↥L := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥L)]
    exact h3
  exact ⟨inclusion hKL k, h4, rfl⟩

private theorem psi_card_dvd {K M : Subgroup X} (hKM : K ≤ M) :
    Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣
      Nat.card ((K.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))) := by
  set f : ↥K →* ↥M ⧸ pPrimeCore 2 ↥M :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (inclusion hKM) with hf
  have hker : f.ker ≤ pPrimeCore 2 ↥K := by
    refine UnbalancedGS.le_pPrimeCore_two_of_normal_odd inferInstance ?_
    have h1 : f.ker = (pPrimeCore 2 ↥M).comap (inclusion hKM) := by
      rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [h1]
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (card_comap_dvd_of_injective _ _ (inclusion_injective hKM))
  have hrange : f.range = (K.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) := by
    rw [hf, MonoidHom.range_comp, inclusion_range]
  rw [← hrange, ← index_ker f]
  exact index_dvd_of_le hker

private theorem psi_normalizer_of_le {Y M K : Subgroup X} {g : X} (hMY : M ≤ Y)
    (hM : IsPComponent 2 (M.subgroupOf Y)) (hgY : g ∈ normalizer (Y : Set X)) (hKM : K ≤ M)
    (hK : ¬ Group.IsSolvable ↥K) (hgK : ∀ k ∈ K, g * k = k * g) :
    g ∈ normalizer (M : Set X) := by
  obtain ⟨hcY, hcpc⟩ := A10T.isPComponent_conjugate hgY hMY hM
  have hKc : K ≤ conjugate M g := fun k hk => by
    rw [UnbalancedLayer.mem_conjugate_iff, hgK k hk, mul_inv_cancel_right]
    exact hKM hk
  have heq := A10T.eq_of_le_of_le_of_not_isSolvable hMY hcY hM hcpc hKM hKc hK
  refine mem_normalizer_iff.mpr fun x => ?_
  have h1 : x ∈ conjugate M g ↔ g * x * g⁻¹ ∈ M := UnbalancedLayer.mem_conjugate_iff
  rw [← heq] at h1
  exact h1

private theorem psi_kernel_of_cover {Y Ld K : Subgroup X} {b : X} (hLdY : Ld ≤ Y)
    (hLd : IsPComponent 2 (Ld.subgroupOf Y)) (hbY : b ∈ normalizer (Y : Set X))
    (hKLd : K ⊔ (pPrimeCore 2 ↥Ld).map Ld.subtype = Ld) (hK : ¬ Group.IsSolvable ↥K)
    (hbK : ∀ k ∈ K, b * k = k * b) : b ∈ coreActionKernel Ld :=
  psi_kernel_of_sup hKLd
    (psi_normalizer_of_le hLdY hLd hbY (le_sup_left.trans_eq hKLd) hK hbK) hbK

private theorem psi_open_sup {C Ld K : Subgroup X} {b : X} (hLdC : Ld ≤ C)
    (hLd : IsPComponent 2 (Ld.subgroupOf C)) (hbC : b ∈ C) (hb2 : IsPGroup 2 (zpowers b))
    (hbK : b ∈ coreActionKernel Ld) (hKLd : K ⊔ (pPrimeCore 2 ↥Ld).map Ld.subtype = Ld)
    (hKb : K ≤ centralizer ({b} : Set X)) :
    Open.IsSubnormal (K ⊔ oddCoreIn (C ⊓ centralizer ({b} : Set X)))
      (C ⊓ centralizer ({b} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := C ⊓ centralizer ({b} : Set X)
  set Ldb := GSLit.fixedLayer Ld (zpowers b)
  have hLdq := A10T.isQuasisimple_of_isPComponent hLdC hLd
  obtain ⟨-, -, hLds, -, -⟩ := id hLd
  have hbK' : zpowers b ≤ coreActionKernel Ld := zpowers_le.mpr hbK
  have hpc := GSLit.fixedLayer_isPComponent hLdC hLds (zpowers_le.mpr hbC) hbK' hb2 hLdq
  rw [centralizer_zpowers_eq] at hpc
  have hLdbH : Ldb ≤ H := by
    have h1 := (GSLit.fixedLayer_le_inf Ld (zpowers b)).trans (inf_le_inf_right _ hLdC)
    rwa [centralizer_zpowers_eq] at h1
  have hLdbsup := (GSLit.fixedLayer_sup_pPrimeCore hLdq hbK' hb2).1
  have hOLd : (pPrimeCore 2 ↥Ld).map Ld.subtype ≤ oddCoreIn C := by
    intro x hx
    have hxC : x ∈ C := hLdC (map_subtype_le _ hx)
    have h1 := GSLit.map_pPrimeCore_subgroupOf_le hLdC hLd
      (mem_subgroupOf.mpr hx : (⟨x, hxC⟩ : ↥C) ∈ _)
    exact ⟨⟨x, hxC⟩, h1, rfl⟩
  have hCO : H ≤ normalizer (oddCoreIn C : Set X) := fun h hh =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic C (pPrimeCore 2 ↥C)
      (le_normalizer (mem_inf.mp hh).1)
  have hHO : H ⊓ oddCoreIn C ≤ oddCoreIn H :=
    UnbalancedGS.inf_le_map_pPrimeCore_two hCO (UnbalancedGS.odd_card_map_pPrimeCore_two C)
  have hkey : ∀ {x y o : X}, x ∈ centralizer ({b} : Set X) → y ∈ centralizer ({b} : Set X) →
      o ∈ (pPrimeCore 2 ↥Ld).map Ld.subtype → y * o = x → o ∈ oddCoreIn H := by
    intro x y o hx hy ho hyo
    have hob : o ∈ centralizer ({b} : Set X) := by
      have h1 : o = y⁻¹ * x := by rw [← hyo]; group
      rw [h1]
      exact mul_mem (inv_mem hy) hx
    exact hHO (mem_inf.mpr ⟨mem_inf.mpr ⟨hLdC (map_subtype_le _ ho), hob⟩, hOLd ho⟩)
  have hONLd : ∀ {A : Subgroup X}, A ≤ Ld →
      A ≤ normalizer (((pPrimeCore 2 ↥Ld).map Ld.subtype : Subgroup X) : Set X) :=
    fun hA x hx => UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Ld
      (pPrimeCore 2 ↥Ld) (le_normalizer (hA hx))
  have hKLd' : K ≤ Ld := le_sup_left.trans_eq hKLd
  have hLdbLd : Ldb ≤ Ld := (GSLit.fixedLayer_le_inf Ld (zpowers b)).trans inf_le_left
  have hLdbb : Ldb ≤ centralizer ({b} : Set X) := hLdbH.trans inf_le_right
  have heq : Ldb ⊔ oddCoreIn H = K ⊔ oddCoreIn H := by
    apply le_antisymm
    · refine sup_le (fun x hx => ?_) le_sup_right
      have hx' : x ∈ K ⊔ (pPrimeCore 2 ↥Ld).map Ld.subtype := by
        rw [hKLd]
        exact hLdbLd hx
      obtain ⟨k, hk, o, ho, rfl⟩ := (UnbalancedGS.mem_sup_iff_exists_mul (hONLd hKLd')).mp hx'
      exact mul_mem (mem_sup_left hk) (mem_sup_right (hkey (hLdbb hx) (hKb hk) ho rfl))
    · refine sup_le (fun x hx => ?_) le_sup_right
      have hx' : x ∈ Ldb ⊔ (pPrimeCore 2 ↥Ld).map Ld.subtype := by
        rw [hLdbsup]
        exact hKLd' hx
      obtain ⟨y, hy, o, ho, rfl⟩ := (UnbalancedGS.mem_sup_iff_exists_mul (hONLd hLdbLd)).mp hx'
      exact mul_mem (mem_sup_left hy) (mem_sup_right (hkey (hKb hx) (hLdbb hy) ho rfl))
  obtain ⟨-, -, hLdbs, -, -⟩ := id hpc
  have hHON : H ≤ normalizer (oddCoreIn H : Set X) := fun h hh =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic H (pPrimeCore 2 ↥H)
      (le_normalizer hh)
  have h1 := Eight2.Three.open_sup (Eight2.Three.open_of_isSubnormal hLdbH hLdbs) hHON
  have hOH : H ⊔ oddCoreIn H = H := sup_eq_left.mpr (map_subtype_le _)
  rwa [heq, hOH] at h1

private theorem psi_exists_centralizer_mk {M E : Subgroup X} (hE : IsPGroup 2 E)
    (hEN : E ≤ normalizer (M : Set X)) (w : ↥M)
    (hw : ∀ (e : X) (he : e ∈ E), QuotientGroup.mk' (pPrimeCore 2 ↥M)
      (M.normalizerMonoidHom ⟨e, hEN he⟩ w) = QuotientGroup.mk' (pPrimeCore 2 ↥M) w) :
    ∃ c : ↥M, (c : X) ∈ centralizer (E : Set X) ∧
      QuotientGroup.mk' (pPrimeCore 2 ↥M) c = QuotientGroup.mk' (pPrimeCore 2 ↥M) w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  let _ := SignalizerFunctor.Helpers.conjugationAction E M hEN
  have hsmul : ∀ (e : ↥E) (v : ↥M), e • v = M.normalizerMonoidHom ⟨e, hEN e.2⟩ v :=
    fun _ _ => rfl
  have hO : ∀ (e : ↥E) (o : ↥M), o ∈ pPrimeCore 2 ↥M →
      M.normalizerMonoidHom ⟨e, hEN e.2⟩ o ∈ pPrimeCore 2 ↥M := by
    intro e o ho
    rw [← pPrimeCore_map_iso 2 (M.normalizerMonoidHom ⟨e, hEN e.2⟩)]
    exact mem_map_of_mem _ ho
  let fibre : SubMulAction E ↥M := ⟨{v | ρ v = ρ w}, by
    intro e v hv
    change ρ (e • v) = ρ w
    rw [hsmul, ← hw e e.2]
    change ρ v = ρ w at hv
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hv ⊢
    rw [← map_inv, ← map_mul]
    exact hO e _ hv⟩
  have hfibre : Nat.card fibre = Nat.card (pPrimeCore 2 ↥M) := by
    have heq : {v : ↥M | ρ v = ρ w} = ρ ⁻¹' {ρ w} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥M)]
    exact (Nat.card_congr (Set.equivOfEq heq)).trans (Nat.card_congr (ρ.fiberEquivKer w))
  have hnd : ¬ 2 ∣ Nat.card fibre := by
    rw [hfibre]
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  obtain ⟨c, hc⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card fibre hnd
  refine ⟨c.val, mem_centralizer_iff.mpr fun e he => ?_, c.2⟩
  have h1 := congrArg (fun v : fibre => ((v.val : ↥M) : X)) (hc ⟨e, he⟩)
  change e * c.val * e⁻¹ = c.val at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

private theorem psi_map_fixed {M : Subgroup X} {d : X}
    (hdN : d ∈ normalizer (M : Set X)) (hd : IsPGroup 2 (zpowers d)) :
    ((M ⊓ centralizer ({d} : Set X)).subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) =
      fixedSubgroup (Eight.oddBarAction M ⟨d, hdN⟩) := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    have hm' : (m : X) ∈ centralizer ({d} : Set X) := (mem_inf.mp (mem_subgroupOf.mp hm)).2
    exact Eight.mem_fixedPoints_oddBarAction ⟨d, hdN⟩ (mem_centralizer_singleton_iff.mp hm').symm
  · intro x hx
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) x
    have hEN : zpowers d ≤ normalizer (M : Set X) := zpowers_le.mpr hdN
    obtain ⟨c, hcC, hcw⟩ := psi_exists_centralizer_mk hd hEN w (by
      intro e he
      have hsub : zpowers d ≤ ((MulAction.stabilizer (MulAut (↥M ⧸ pPrimeCore 2 ↥M))
          (QuotientGroup.mk' (pPrimeCore 2 ↥M) w)).comap (Eight.oddBarAction M)).map
          (normalizer (M : Set X)).subtype := by
        rw [zpowers_le]
        exact ⟨⟨d, hdN⟩, MulAction.mem_stabilizer_iff.mpr hx, rfl⟩
      obtain ⟨e', he', hee'⟩ := hsub he
      have h1 : (⟨e, hEN he⟩ : normalizer (M : Set X)) = e' := Subtype.ext hee'.symm
      have h2 := MulAction.mem_stabilizer_iff.mp (mem_comap.mp he')
      rw [← h1] at h2
      exact h2)
    refine ⟨c, mem_subgroupOf.mpr (mem_inf.mpr ⟨c.2, ?_⟩), hcw⟩
    rw [← centralizer_zpowers_eq]
    exact hcC

private theorem psi_subnormal_fixed {M H K : Subgroup X} {d : X}
    (hdN : d ∈ normalizer (M : Set X)) (hd : IsPGroup 2 (zpowers d))
    (hKM : K ≤ M ⊓ centralizer ({d} : Set X)) (hMH : M ⊓ centralizer ({d} : Set X) ≤ H)
    (hU : Open.IsSubnormal (K ⊔ oddCoreIn H) H) :
    ((((K.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))) ⊔
      oddCoreIn (fixedSubgroup (Eight.oddBarAction M ⟨d, hdN⟩))).subgroupOf
        (fixedSubgroup (Eight.oddBarAction M ⟨d, hdN⟩))).IsSubnormal := by
  set C := M ⊓ centralizer ({d} : Set X)
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  set F := fixedSubgroup (Eight.oddBarAction M ⟨d, hdN⟩)
  set T := (K.subgroupOf M).map π
  have hF : (C.subgroupOf M).map π = F := psi_map_fixed hdN hd
  have hCM : C ≤ M := inf_le_left
  have hHO : H ≤ normalizer (oddCoreIn H : Set X) := fun h hh =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic H (pPrimeCore 2 ↥H)
      (le_normalizer hh)
  have hKO : K ≤ normalizer (oddCoreIn H : Set X) := (hKM.trans hMH).trans hHO
  set V := (K ⊔ oddCoreIn H) ⊓ C
  have hVs : Open.IsSubnormal V C := hU.inf_of_le hMH
  have hVs' : Open.IsSubnormal ((V.subgroupOf M).map π) F := by
    have h1 := (hVs.comap M.subtype).map π
    rw [← hF]
    exact h1
  set N := (oddCoreIn H ⊓ C).subgroupOf M with hN
  have hNF : N.map π ≤ oddCoreIn F := by
    have hNC : N ≤ C.subgroupOf M := fun x hx =>
      mem_subgroupOf.mpr (mem_inf.mp (mem_subgroupOf.mp hx)).2
    have hNF' : N.map π ≤ F := by
      rw [← hF]
      exact map_mono hNC
    have hCN : C.subgroupOf M ≤ normalizer (N : Set ↥M) := by
      intro g hg
      apply le_normalizer_comap M.subtype
      have hgC : (g : X) ∈ C := mem_subgroupOf.mp hg
      exact inf_normalizer_le_normalizer_inf ⟨hHO (hMH hgC), le_normalizer hgC⟩
    have hFN : F ≤ normalizer ((N.map π : Subgroup _) : Set _) := by
      rw [← hF]
      exact (map_mono hCN).trans (le_normalizer_map π)
    have hodd : Odd (Nat.card (N.map π)) := by
      refine Odd.of_dvd_nat ?_ (card_map_dvd N π)
      rw [hN, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right.trans hCM)).toEquiv]
      exact Odd.of_dvd_nat (UnbalancedGS.odd_card_map_pPrimeCore_two H)
        (card_dvd_of_le inf_le_left)
    have h1 := UnbalancedGS.inf_le_map_pPrimeCore_two hFN hodd
    rwa [inf_of_le_right hNF'] at h1
  have hVT : (V.subgroupOf M).map π ≤ T ⊔ oddCoreIn F := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨hvKO, hvC⟩ := mem_inf.mp (mem_subgroupOf.mp hv)
    obtain ⟨k, hk, o, ho, hko⟩ := (UnbalancedGS.mem_sup_iff_exists_mul hKO).mp hvKO
    have hkC : k ∈ C := hKM hk
    have hoC : o ∈ C := by
      have h1 : o = k⁻¹ * v := by rw [← hko]; group
      rw [h1]
      exact mul_mem (inv_mem hkC) hvC
    have hv2 : v = ⟨k, hCM hkC⟩ * ⟨o, hCM hoC⟩ := Subtype.ext hko.symm
    rw [hv2, map_mul]
    exact mul_mem (mem_sup_left (mem_map_of_mem π (mem_subgroupOf.mpr hk)))
      (mem_sup_right (hNF (mem_map_of_mem π (mem_subgroupOf.mpr (mem_inf.mpr ⟨ho, hoC⟩)))))
  have hTV : T ≤ (V.subgroupOf M).map π := map_mono fun x hx =>
    mem_subgroupOf.mpr (mem_inf.mpr ⟨mem_sup_left (mem_subgroupOf.mp hx),
      hKM (mem_subgroupOf.mp hx)⟩)
  have heq : (V.subgroupOf M).map π ⊔ oddCoreIn F = T ⊔ oddCoreIn F :=
    le_antisymm (sup_le hVT le_sup_right) (sup_le_sup_right hTV _)
  have hFO : F ≤ normalizer (oddCoreIn F : Set _) := fun g hg =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic F (pPrimeCore 2 ↥F)
      (le_normalizer hg)
  have h2 := Eight2.Three.open_sup hVs' hFO
  have hOF : F ⊔ oddCoreIn F = F := sup_eq_left.mpr (map_subtype_le _)
  rw [heq, hOF] at h2
  exact h2.subgroupOf

end Q3Psi

namespace Eight2.CtxA0

open Q3Psi

variable {X : Type} [Group X] [Finite X] (c : CtxA0 X)

private theorem psi_card_J (hq3 : c.s.p = 3 ∧ c.s.f = 1) :
    Nat.card (↥c.s.h.J ⧸ pPrimeCore 2 ↥c.s.h.J) = 360 := by
  obtain ⟨eJ⟩ := c.s.sec_J_equiv
  have h1 := c.s.J_type
  rw [hq3.1, hq3.2] at h1
  rw [← Nat.card_congr eJ.toEquiv]
  exact card_of_isSec8JType_three h1

private theorem psi_JE (hq3 : c.s.p = 3 ∧ c.s.f = 1) {d : X} (hdP : d ∈ c.s.h.P) :
    GSLit.fixedLayer c.s.h.J (zpowers c.b ⊔ zpowers d) ≤ centralizer ({c.s.h.a} : Set X) ⊓
        (centralizer ({c.b} : Set X) ⊓ centralizer ({d} : Set X)) ∧
      IsPComponent 2 ((GSLit.fixedLayer c.s.h.J (zpowers c.b ⊔ zpowers d)).subgroupOf
        (centralizer ({c.s.h.a} : Set X) ⊓
          (centralizer ({c.b} : Set X) ⊓ centralizer ({d} : Set X)))) ∧
      Nat.card (↥(GSLit.fixedLayer c.s.h.J (zpowers c.b ⊔ zpowers d)) ⧸
        pPrimeCore 2 ↥(GSLit.fixedLayer c.s.h.J (zpowers c.b ⊔ zpowers d))) = 360 ∧
      GSLit.fixedLayer c.s.h.J (zpowers c.b ⊔ zpowers d) ≤
        GSLit.fixedLayer c.s.h.J (zpowers c.b) ∧
      GSLit.fixedLayer c.s.h.J (zpowers c.b ⊔ zpowers d) ⊔
          (pPrimeCore 2 ↥(UnbalancedGS.gsFixedLayer c.s.h.J d)).map
            (UnbalancedGS.gsFixedLayer c.s.h.J d).subtype =
        UnbalancedGS.gsFixedLayer c.s.h.J d := by
  set E := zpowers c.b ⊔ zpowers d
  have hP2 : IsPGroup 2 c.s.h.P := (B5a.isPGroup_S c.s.h).to_le inf_le_left
  have hEP : E ≤ c.s.h.P := sup_le (zpowers_le.mpr c.hbP) (zpowers_le.mpr hdP)
  have hE2 : IsPGroup 2 E := hP2.to_le hEP
  have hEK : E ≤ coreActionKernel c.s.h.J := hEP.trans inf_le_right
  have hECa : E ≤ centralizer ({c.s.h.a} : Set X) :=
    hEP.trans (inf_le_left.trans (c.s.h.S_le.trans inf_le_left))
  have hCE : centralizer (E : Set X) =
      centralizer ({c.b} : Set X) ⊓ centralizer ({d} : Set X) := by
    apply le_antisymm
    · intro x hx
      exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hx c.b (mem_sup_left (mem_zpowers _))).symm,
        mem_centralizer_singleton_iff.mpr
          (mem_centralizer_iff.mp hx d (mem_sup_right (mem_zpowers _))).symm⟩
    · intro x hx
      obtain ⟨hxb, hxd⟩ := mem_inf.mp hx
      have hEx : E ≤ centralizer ({x} : Set X) :=
        sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hxb).symm))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
            (mem_centralizer_singleton_iff.mp hxd).symm))
      exact mem_centralizer_iff.mpr fun e he => (mem_centralizer_singleton_iff.mp (hEx he))
  have hJq := B5a.isQuasisimple_J c.s.h
  obtain ⟨-, -, hJs, -, -⟩ := id c.s.h.isPComponent_J
  have hpc := GSLit.fixedLayer_isPComponent c.s.h.J_le hJs hECa hEK hE2 hJq
  rw [hCE] at hpc
  have hle : GSLit.fixedLayer c.s.h.J E ≤ centralizer ({c.s.h.a} : Set X) ⊓
      (centralizer ({c.b} : Set X) ⊓ centralizer ({d} : Set X)) := by
    have h1 := (GSLit.fixedLayer_le_inf c.s.h.J E).trans (inf_le_inf_right _ c.s.h.J_le)
    rwa [hCE] at h1
  obtain ⟨eE⟩ := QPUJ.nonempty_fixedLayer_quot_equiv hJq hEK hE2
  refine ⟨hle, hpc, ?_, (GSLit.fixedLayer_nested hJq hEK hE2 le_sup_left).1, ?_⟩
  · rw [Nat.card_congr eE.toEquiv]
    exact c.psi_card_J hq3
  · have h1 := (GSLit.fixedLayer_nested hJq hEK hE2 (le_sup_right : zpowers d ≤ E)).2
    rwa [GSLit.fixedLayer_zpowers] at h1

private theorem psi_mem_secB0 {M : Subgroup X} (hMC : M ≤ centralizer ({c.b} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c.b} : Set X))))
    (hLM : Seven.Lay c.s.h c.s.y ≤ M)
    (eM : Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃*
      ↥(Seven.Lay c.s.h c.s.y) ⧸ pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y)))
    {w₀ : X} (hw₀P : w₀ ∈ c.s.h.P) (hw₀M : w₀ ∈ coreActionKernel M) :
    w₀ ∈ c.s.h.secB0 c.s.y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := Seven.Lay c.s.h c.s.y
  set B₀ := c.s.h.secB0 c.s.y
  have hLO : L ⊔ (pPrimeCore 2 ↥M).map M.subtype = M := by
    obtain ⟨e⟩ := eM
    rw [UnbalancedGS.sup_primeCore_eq_iff_map_eq_top hLM]
    apply Subgroup.eq_top_of_card_eq
    refine Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card _) ?_
    rw [Nat.card_congr e.toEquiv]
    exact psi_card_dvd hLM
  have hLC : L ≤ centralizer (B₀ : Set X) := c.s.Lay_le_centralizer
  have hLns : ¬ Group.IsSolvable ↥L :=
    A10T.not_isSolvable_of_isQuasisimple (A10T.isQuasisimple_of_isPComponent hLC c.s.L_pc)
  have hB₀M : B₀ ≤ coreActionKernel M := by
    intro β hβ
    have hβL : ∀ l ∈ L, β * l = l * β := fun l hl => mem_centralizer_iff.mp (hLC hl) β hβ
    exact psi_kernel_of_sup hLO
      (psi_normalizer_of_le hMC hMpc (le_normalizer (c.secB0_le_centralizer_b hβ)) hLM hLns
        hβL) hβL
  set Q := B₀ ⊔ zpowers w₀
  have hP2 : IsPGroup 2 c.s.h.P := (B5a.isPGroup_S c.s.h).to_le inf_le_left
  have hQP : Q ≤ c.s.h.P := sup_le c.s.B0_le_P (zpowers_le.mpr hw₀P)
  have hQM : Q ≤ coreActionKernel M := sup_le hB₀M (zpowers_le.mpr hw₀M)
  have hQ2 : IsPGroup 2 Q := hP2.to_le hQP
  by_contra hw₀B
  have hlt : B₀.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hw₀B ?_
    have h1 : (⟨w₀, mem_sup_right (mem_zpowers w₀)⟩ : ↥Q) ∈ B₀.subgroupOf Q := by
      rw [htop]
      exact mem_top _
    exact mem_subgroupOf.mp h1
  haveI : Group.IsNilpotent ↥Q := hQ2.isNilpotent
  obtain ⟨w, hwN, hwB⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq (le_sup_left : B₀ ≤ Q)] at hwN
  have hwN' : (w : X) ∈ normalizer (B₀ : Set X) := mem_subgroupOf.mp hwN
  have hwB' : (w : X) ∉ B₀ := fun h => hwB (mem_subgroupOf.mpr h)
  have hwP : (w : X) ∈ c.s.h.P := hQP w.2
  have hwM : (w : X) ∈ coreActionKernel M := hQM w.2
  have hwL : (w : X) ∈ coreActionKernel L := by
    have hwNL : (w : X) ∈ normalizer (L : Set X) :=
      Seven.secG0_le_normalizer_Lay c.s.h c.s.y hwN'
    refine mem_coreActionKernel.mpr ⟨hwNL, fun l hl => ?_⟩
    have h1 : l⁻¹ * (w : X)⁻¹ * l * w ∈ (pPrimeCore 2 ↥M).map M.subtype :=
      (mem_coreActionKernel.mp hwM).2 l (hLM hl)
    have h2 : l⁻¹ * (w : X)⁻¹ * l * w ∈ L := by
      have h3 := (mem_normalizer_iff.mp (inv_mem hwNL) l).mp hl
      rw [inv_inv] at h3
      rw [show l⁻¹ * (w : X)⁻¹ * l * w = l⁻¹ * ((w : X)⁻¹ * l * w) by group]
      exact mul_mem (inv_mem hl) h3
    have hLON : L ≤ normalizer (((pPrimeCore 2 ↥M).map M.subtype : Subgroup X) : Set X) :=
      fun x hx => UnbalancedGS.normalizer_le_normalizer_map_of_characteristic M
        (pPrimeCore 2 ↥M) (le_normalizer (hLM hx))
    exact UnbalancedGS.inf_le_map_pPrimeCore_two hLON
      (UnbalancedGS.odd_card_map_pPrimeCore_two M) (mem_inf.mpr ⟨h2, h1⟩)
  have hwC0 : (w : X) ∈ c.s.h.secC0 c.s.y :=
    mem_inf.mpr ⟨(mem_inf.mp (c.s.h.S_le (c.s.h.P_le_S hwP))).1, hwN'⟩
  obtain ⟨k, hk⟩ := hP2 ⟨(w : X), hwP⟩
  have hk' : (w : X) ^ 2 ^ k = 1 := by
    have h1 := congrArg Subtype.val hk
    simpa using h1
  exact hwB' (c.mem_secB0_of_mem_coreActionKernel hk' hwC0 hwL)

private theorem psi_false (hS : SchreierFor Blueprint.Catalog) (hQ : CFQPUJ6Three)
    (hG : L43FixedA6Input)
    (hA : ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)))
    (hq3 : c.s.p = 3 ∧ c.s.f = 1) {d : X} (hdP : d ∈ c.s.h.P) (hd2 : orderOf d = 2)
    (hdb : d * c.b = c.b * d) (hdnot : d ∉ zpowers c.s.h.a ⊔ c.s.h.secB0 c.s.y)
    {Ld : Subgroup X} (hLd : UnbalancedGS.GSIsoCorr c.s.h.a c.s.h.J d Ld) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdd : d * d = 1 := by rw [← pow_two, ← hd2, pow_orderOf_eq_one]
  have hd2' : IsPGroup 2 (zpowers d) :=
    Pump516.isPGroup_zpowers_of_pow ⟨1, by rw [pow_one, pow_two, hdd]⟩
  obtain ⟨hcorr, -, hsup⟩ := UnbalancedGS.gsIsoCorr_iff_sup.mp hLd
  obtain ⟨-, -, -, -, -, hLdC, hLdpc, -⟩ := hcorr
  obtain ⟨hJEle, hJEpc, hJEcard, hJEJb, hJEd⟩ := c.psi_JE hq3 hdP
  set JE := GSLit.fixedLayer c.s.h.J (zpowers c.b ⊔ zpowers d)
  set Jd := UnbalancedGS.gsFixedLayer c.s.h.J d
  have hJEns := A10T.not_isSolvable_of_isQuasisimple
    (A10T.isQuasisimple_of_isPComponent hJEle hJEpc)
  have hJEb : JE ≤ centralizer ({c.b} : Set X) := fun x hx =>
    (mem_inf.mp (mem_inf.mp (hJEle hx)).2).1
  have hJEdC : JE ≤ centralizer ({d} : Set X) := fun x hx =>
    (mem_inf.mp (mem_inf.mp (hJEle hx)).2).2
  have hJdLd : Jd ≤ Ld := le_sup_left.trans_eq hsup
  have hJEJd : JE ≤ Jd := le_sup_left.trans_eq hJEd
  have hJELd : JE ⊔ (pPrimeCore 2 ↥Ld).map Ld.subtype = Ld := by
    refine le_antisymm (sup_le (hJEJd.trans hJdLd) (map_subtype_le _)) ?_
    calc Ld = Jd ⊔ (pPrimeCore 2 ↥Ld).map Ld.subtype := hsup.symm
      _ ≤ JE ⊔ (pPrimeCore 2 ↥Ld).map Ld.subtype := by
        refine sup_le ?_ le_sup_right
        calc Jd = JE ⊔ (pPrimeCore 2 ↥Jd).map Jd.subtype := hJEd.symm
          _ ≤ _ := sup_le le_sup_left
            ((psi_oddCore_le hJdLd hsup).trans le_sup_right)
  have hbCd : c.b ∈ centralizer ({d} : Set X) := mem_centralizer_singleton_iff.mpr hdb.symm
  have hbK : c.b ∈ coreActionKernel Ld :=
    psi_kernel_of_cover hLdC hLdpc (le_normalizer hbCd) hJELd hJEns
      (fun k hk => (mem_centralizer_singleton_iff.mp (hJEb hk)).symm)
  have hU := psi_open_sup hLdC hLdpc hbCd c.isPGroup_zpowers_b hbK hJELd hJEb
  obtain ⟨M, hMC, hMpc, hLM, hJbM, eM, hLie⟩ := c.exists_pComponent_l43 hS hQ hA hq3
  have hJEM : JE ≤ M := hJEJb.trans hJbM
  have hdCb : d ∈ centralizer ({c.b} : Set X) := mem_centralizer_singleton_iff.mpr hdb
  have hdN : d ∈ normalizer (M : Set X) :=
    psi_normalizer_of_le hMC hMpc (le_normalizer hdCb) hJEM hJEns
      (fun k hk => (mem_centralizer_singleton_iff.mp (hJEdC hk)).symm)
  set α := Eight.oddBarAction M ⟨d, hdN⟩ with hαdef
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  set T := (JE.subgroupOf M).map π
  set ℓ := π ⟨c.s.h.a * c.b, hLM c.ab_mem_Lay⟩ with hℓdef
  have hαα : α * α = 1 := by
    rw [hαdef, ← map_mul]
    have h1 : (⟨d, hdN⟩ : normalizer (M : Set X)) * ⟨d, hdN⟩ = 1 := Subtype.ext hdd
    rw [h1, map_one]
  have hαT : ∀ t ∈ T, α t = t := by
    rintro _ ⟨j, hj, rfl⟩
    exact Eight.mem_fixedPoints_oddBarAction ⟨d, hdN⟩
      (mem_centralizer_singleton_iff.mp (hJEdC (mem_subgroupOf.mp hj))).symm
  have hab2 : (⟨c.s.h.a * c.b, hLM c.ab_mem_Lay⟩ : ↥M) * ⟨c.s.h.a * c.b, hLM c.ab_mem_Lay⟩ =
      1 := Subtype.ext c.ab_mul_ab
  have hℓℓ : ℓ * ℓ = 1 := by rw [hℓdef, ← map_mul, hab2, map_one]
  have hℓ2 : orderOf ℓ = 2 := by
    refine orderOf_eq_prime (by rw [pow_two, hℓℓ]) fun h => ?_
    have hR : IsPGroup 2 (zpowers (⟨c.s.h.a * c.b, hLM c.ab_mem_Lay⟩ : ↥M)) :=
      Pump516.isPGroup_zpowers_of_pow ⟨1, by rw [pow_one, pow_two, hab2]⟩
    have h1 := OddQuot.injOn_of_isPGroup hR (mem_zpowers _) (one_mem _)
      (h.trans (map_one π).symm)
    exact c.ab_ne_one (congrArg Subtype.val h1)
  have hTC : T ≤ centralizer ({ℓ} : Set _) := by
    rintro _ ⟨j, hj, rfl⟩
    have hja : Commute (j : X) c.s.h.a :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp (hJEle (mem_subgroupOf.mp hj))).1
    have hjb : Commute (j : X) c.b :=
      mem_centralizer_singleton_iff.mp (hJEb (mem_subgroupOf.mp hj))
    have h1 : j * ⟨c.s.h.a * c.b, hLM c.ab_mem_Lay⟩ = ⟨c.s.h.a * c.b, hLM c.ab_mem_Lay⟩ * j :=
      Subtype.ext (hja.mul_right hjb)
    rw [mem_centralizer_singleton_iff, hℓdef, ← map_mul, ← map_mul, h1]
  have hTperf : Group.IsPerfect ↥T := by
    haveI := A10T.isPerfect_of_isPComponent hJEle hJEpc
    haveI : Group.IsPerfect ↥(JE.subgroupOf M) := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hJEM).symm.toMonoidHom)
      (subgroupOfEquivOfLe hJEM).symm.surjective
    exact Group.IsPerfect.ofSurjective (f := π.subgroupMap (JE.subgroupOf M))
      (π.subgroupMap_surjective _)
  have h360 : 360 ∣ Nat.card T := by
    have h1 := psi_card_dvd hJEM
    rwa [hJEcard] at h1
  have hsub := psi_subnormal_fixed hdN hd2' (le_inf hJEM hJEdC)
    (fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, hMC (mem_inf.mp hx).1⟩) hU
  rcases hG _ hLie ℓ hℓ2 T hTC hTperf h360 α hαα hαT hsub with h1 | h1
  ·
    have hdK : d ∈ coreActionKernel M := Eight.mem_ker_oddBarAction.mp
      (show (⟨d, hdN⟩ : normalizer (M : Set X)) ∈ (Eight.oddBarAction M).ker from
        MonoidHom.mem_ker.mpr h1)
    exact hdnot (mem_sup_right (c.psi_mem_secB0 hMC hMpc hLM eM hdP hdK))
  ·
    have hbN : c.b ∈ normalizer (M : Set X) := centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun m hm => mem_centralizer_singleton_iff.mp (hMC hm))
    have habN : c.s.h.a * c.b ∈ normalizer (M : Set X) := le_normalizer (hLM c.ab_mem_Lay)
    have haN : c.s.h.a ∈ normalizer (M : Set X) := by
      have h2 := mul_mem habN hbN
      rwa [mul_assoc, c.hbb, mul_one] at h2
    have hb1 : Eight.oddBarAction M ⟨c.b, hbN⟩ = 1 := by
      ext x
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
      rw [Eight.oddBarAction_apply_mk, MulAut.one_apply]
      congr 1
      exact Subtype.ext (show c.b * (m : X) * c.b⁻¹ = m by
        rw [← mem_centralizer_singleton_iff.mp (hMC m.2), mul_inv_cancel_right])
    have ha : Eight.oddBarAction M ⟨c.s.h.a, haN⟩ = MulAut.conj ℓ := by
      have e1 : (⟨c.s.h.a, haN⟩ : normalizer (M : Set X)) =
          ⟨c.s.h.a * c.b, habN⟩ * ⟨c.b, hbN⟩ :=
        Subtype.ext (show c.s.h.a = c.s.h.a * c.b * c.b by rw [mul_assoc, c.hbb, mul_one])
      rw [e1, map_mul, hb1, mul_one]
      exact Eight.oddBarAction_of_mem ⟨c.s.h.a * c.b, hLM c.ab_mem_Lay⟩
    have hadN : c.s.h.a * d ∈ normalizer (M : Set X) := mul_mem haN hdN
    have had : Eight.oddBarAction M ⟨c.s.h.a * d, hadN⟩ = 1 := by
      have e2 : (⟨c.s.h.a * d, hadN⟩ : normalizer (M : Set X)) = ⟨c.s.h.a, haN⟩ * ⟨d, hdN⟩ :=
        rfl
      rw [e2, map_mul, ha, ← hαdef, h1, ← map_mul, hℓℓ, map_one]
    have hadK : c.s.h.a * d ∈ coreActionKernel M := Eight.mem_ker_oddBarAction.mp
      (show (⟨c.s.h.a * d, hadN⟩ : normalizer (M : Set X)) ∈ (Eight.oddBarAction M).ker from
        MonoidHom.mem_ker.mpr had)
    have hadB := c.psi_mem_secB0 hMC hMpc hLM eM (mul_mem c.s.h.a_mem_P hdP) hadK
    apply hdnot
    have h2 : d = c.s.h.a⁻¹ * (c.s.h.a * d) := by group
    rw [h2]
    exact mul_mem (mem_sup_left (inv_mem (mem_zpowers _))) (mem_sup_right hadB)

end Eight2.CtxA0

theorem gs82LemmaPsi_of_l43 (hS : SchreierFor Blueprint.Catalog) (hQ : CFQPUJ6Three)
    (hG : L43FixedA6Input) : GS82LemmaPsi := by
  intro X _ _ c hA hp hf d hdP hd2 hdb hdnot ⟨Ld, hLd⟩
  exact c.psi_false hS hQ hG hA ⟨hp, hf⟩ hdP hd2 hdb hdnot hLd

end CFSG.ComponentClassification.GSThmB
