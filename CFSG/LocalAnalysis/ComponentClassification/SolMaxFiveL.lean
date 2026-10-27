module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveF
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Make
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbal
public import Certificates.Certificate23331

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem l34GraphUnitaryCheck_spec (h : L34Graph.l34GraphUnitaryCheck = true) :
    ∀ u ∈ (orbitR r₄T).tabs.toList, (comp 42 u r₃T == comp 42 r₃T u) = true →
      ∀ s ∈ (centS r₃T).toList, ∃ x ∈ (centS r₃T).toList,
        (comp 42 (comp 42 (comp 42 u x) u) s == comp 42 s x) = false := by
  intro u hu huc s hs
  have h' : ((orbitR r₄T).tabs.toList.all fun u => !(comp 42 u r₃T == comp 42 r₃T u) ||
      ((centS r₃T).toList.all fun s => (centS r₃T).toList.any fun x =>
        !(comp 42 (comp 42 (comp 42 u x) u) s == comp 42 s x))) = true := h
  rw [List.all_eq_true] at h'
  have h2 := h' u hu
  rw [huc, Bool.not_true, Bool.false_or, List.all_eq_true] at h2
  obtain ⟨x, hx, hx'⟩ := List.any_eq_true.mp (h2 s hs)
  exact ⟨x, hx, by simpa using hx'⟩

theorem graphUnitary_parts
    {u s : Perm (Fin 42)} (hu : u ∈ R) (huc : IsConj (⟨u, hu⟩ : R) r₄R)
    (hur : u * r₃ = r₃ * u) (hs : s ∈ C₃) : ∃ x ∈ C₃, u * x * u * s ≠ s * x := by
  classical
  obtain ⟨tu, htu, htuu⟩ := (conjClass₄.1 ⟨u, hu⟩).1 huc
  obtain ⟨ts, hts, htss⟩ := enumerates_C₃.complete s hs
  have hcomm : (comp 42 tu r₃T == comp 42 r₃T tu) = true :=
    ((htuu.comp tabRep_r₃).beq_iff (tabRep_r₃.comp htuu)).mpr hur
  obtain ⟨tx, htx, hne⟩ :=
    l34GraphUnitaryCheck_spec Certificates.certificate23331 tu htu hcomm ts hts
  obtain ⟨x, hx, htxx⟩ := enumerates_C₃.sound tx htx
  refine ⟨x, hx, fun heq => ?_⟩
  have h1 : (comp 42 (comp 42 (comp 42 tu tx) tu) ts == comp 42 ts tx) = true :=
    ((((htuu.comp htxx).comp htuu).comp htss).beq_iff (htss.comp htxx)).mpr heq
  rw [h1] at hne
  exact absurd hne (by decide)

theorem card_centralizer_conj_inf_S {c r : Perm (Fin 42)}
    (hc : c ∈ R) :
    Nat.card ↥(centralizer ({c * r * c⁻¹} : Set (Perm (Fin 42))) ⊓ S) =
      Nat.card ↥(centralizer ({r} : Set (Perm (Fin 42))) ⊓ S) := by
  symm
  refine Nat.card_congr
    { toFun := fun x => ⟨c * x * c⁻¹, mem_inf.2 ⟨?_, conj_mem_S hc (mem_inf.1 x.2).2⟩⟩
      invFun := fun y => ⟨c⁻¹ * y * c, mem_inf.2 ⟨?_, ?_⟩⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group) }
  · have hx := mem_centralizer_singleton_iff.mp (mem_inf.1 x.2).1
    rw [mem_centralizer_singleton_iff]
    calc c * (x : Perm (Fin 42)) * c⁻¹ * (c * r * c⁻¹) = c * ((x : Perm (Fin 42)) * r) * c⁻¹ :=
          by group
      _ = c * (r * x) * c⁻¹ := by rw [hx]
      _ = c * r * c⁻¹ * (c * x * c⁻¹) := by group
  · have hy := mem_centralizer_singleton_iff.mp (mem_inf.1 y.2).1
    rw [mem_centralizer_singleton_iff]
    calc c⁻¹ * (y : Perm (Fin 42)) * c * r = c⁻¹ * ((y : Perm (Fin 42)) * (c * r * c⁻¹)) * c :=
          by group
      _ = c⁻¹ * (c * r * c⁻¹ * y) * c := by rw [hy]
      _ = r * (c⁻¹ * y * c) := by group
  · have h1 := conj_mem_S (inv_mem hc) (mem_inf.1 y.2).2
    rwa [inv_inv] at h1

variable {X : Type} [Group X]

theorem le_of_twoElements_of_residual {L K : Subgroup X}
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥L = ⊤)
    (h : ∀ x ∈ L, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ K) : L ≤ K := by
  have hK' : K.subgroupOf L = ⊤ := by
    rw [eq_top_iff, ← hres]
    refine sSup_le fun P hP => ?_
    intro p hp
    rw [mem_subgroupOf]
    obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
    refine h _ p.2 ⟨k, ?_⟩
    have := congrArg (fun w : ↥P => ((w : ↥L) : X)) hk
    simpa using this
  intro z hz
  have h1 : (⟨z, hz⟩ : ↥L) ∈ K.subgroupOf L := hK' ▸ mem_top _
  exact h1

theorem false_of_mem_cak_of_not_cover [Finite X] {c t : X} {M Jc : Subgroup X}
    (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X)))) (ht2 : t * t = 1)
    (htc : t * c = c * t) (htK : t ∈ UnbalancedLayer.coreActionKernel M) (hJcM : Jc ≤ M)
    (hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))
    (hJcpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))))
    (hcov : ¬ Jc ⊔ (pPrimeCore 2 ↥M).map M.subtype = M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cc := centralizer ({c} : Set X) with hCcdef
  set Ct := centralizer ({t} : Set X) with hCtdef
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M Cc hMC).mp hMpc).2.2
  have hMsub : (M.subgroupOf Cc).IsSubnormal := hMpc.choose_spec.2.1
  have hE : zpowers t ≤ UnbalancedLayer.coreActionKernel M := zpowers_le.mpr htK
  have hE2 : IsPGroup 2 (zpowers t) := isPGroup_zpowers_of_mul_self ht2
  have hEX : zpowers t ≤ Cc := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr htc)
  have hCE : centralizer ((zpowers t : Subgroup X) : Set X) = Ct :=
    UnbalancedLayer.centralizer_zpowers_eq t
  set L := GSLit.fixedLayer M (zpowers t) with hLdef
  have hLpc := GSLit.fixedLayer_isPComponent hMC hMsub hEX hE hE2 hMq
  rw [hCE, inf_comm] at hLpc
  have hle := GSLit.fixedLayer_le_inf M (zpowers t)
  rw [hCE] at hle
  have hLY : L ≤ Ct ⊓ Cc := fun z hz =>
    mem_inf.2 ⟨(mem_inf.1 (hle hz)).2, hMC (mem_inf.1 (hle hz)).1⟩
  obtain ⟨hsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hE hE2
  have hcl := GSLit.fixedLayer_eq_closure hMq hE hE2
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hJcL : Jc ≤ L := le_of_twoElements_of_residual hres fun x hx ⟨k, hk⟩ => by
    rw [hLdef, hcl]
    refine subset_closure ⟨mem_inf.2 ⟨hJcM hx, ?_⟩, ?_⟩
    · rw [hCE]
      exact (mem_inf.1 (hJcC hx)).1
    · obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
      exact ⟨j, hj⟩
  rcases GSLit.eq_or_eq_of_le_sup hJcC hJcpc hLY hLpc hLY hLpc (hJcL.trans le_sup_left) with
    h | h <;> exact hcov (by rw [h]; exact hsup)

theorem signalizerFivePumpLThreeFourInput_of_cert
    (hbal : Sol78.BalanceTwoComponentInput) : SignalizerFivePumpLThreeFourInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj hL
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hMX
  have htri := gsUnbalancingTriple_of_not_balanced hbal hc hao hac hMC hMpc hMX
  have hMperf : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hMC hMpc
  have hunit : GrSLit.IsL34Unitary M a := GrSLit.L34Facts.l34UnbalancingUnitaryStep X c a M htri hL
  obtain ⟨ρ, hρa⟩ := HSFLit.AutL34.exists_real_unitary hMperf hL hunit
  have haM : a ∈ normalizer (M : Set X) := hunit.1
  have ht2 : t * t = 1 := by rw [← sq, ← hpair.1.1, pow_orderOf_eq_one]
  have htM : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
  have hJcM' : Jc ≤ M := by
    have h1 := hJcM
    rwa [hfix, sup_idem] at h1
  have hJcCt : Jc ≤ centralizer ({t} : Set X) := (hJcJ.trans inf_le_left).trans hpair.1.2.1
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    le_inf hJcCt (hJcJ.trans inf_le_right)
  have hJcperf : ⁅Jc, Jc⁆ = Jc := UnbalancedCorr.commutator_eq_of_isPComponent hJcC hJcpc
  have hβ : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  let eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 5) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have hJcN : Jc ≤ normalizer (M : Set X) := fun z hz => le_normalizer (hJcM' hz)
  have hU : Jc ⊓ UnbalancedLayer.coreActionKernel M ≤ coreNOf Jc := by
    rcases le_core_or_eq_of_normal (by norm_num) eJc hJcperf inf_le_left (fun l hl =>
        inf_mem_normalizer' (le_normalizer hl) (mem_normalizer_coreActionKernel (hJcN hl)))
      with h | h
    · exact h
    · refine absurd (fun z hz => ?_) hJcK
      have h1 : z ∈ Jc ⊓ UnbalancedLayer.coreActionKernel M := by
        rw [h]
        exact hz
      exact (mem_inf.1 h1).2
  have hcard1 := ρ.card_eq hJcN
  have hcard2 := card_eq_of_alt (by norm_num) eJc
  have h60 : Nat.factorial 5 / 2 = 60 := by decide
  rw [h60] at hcard2
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hU
  have hUpos : 0 < Nat.card ↥(Jc ⊓ UnbalancedLayer.coreActionKernel M) := Nat.card_pos
  have himg60 : Nat.card (ρ.img Jc) = 60 * k := by
    have h1 : Nat.card (ρ.img Jc) * Nat.card ↥(Jc ⊓ UnbalancedLayer.coreActionKernel M) =
        60 * k * Nat.card ↥(Jc ⊓ UnbalancedLayer.coreActionKernel M) := by
      rw [← hcard1, hcard2, hk]
      ring
    exact Nat.eq_of_mul_eq_mul_right hUpos h1
  set T : Perm (Fin 42) := ρ.φ ⟨t, htM⟩ with hTdef
  have hTR : T ∈ R := ρ.mem_R _
  have hT2 : T * T = 1 := by
    rw [hTdef, ← map_mul]
    convert map_one ρ.φ
    exact Subtype.ext ht2
  have himgT : ρ.img Jc ≤ centralizer ({T} : Set (Perm (Fin 42))) ⊓ S := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hx
    refine mem_inf.2 ⟨?_, ρ.map_K (g : X) (hJcM' hg)⟩
    rw [mem_centralizer_singleton_iff, hTdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJcCt hg))
  have hT1 : T ≠ 1 := fun hT => false_of_mem_cak_of_not_cover hMC hMpc ht2 htc
    ((ρ.ker_iff ⟨t, htM⟩).1 hT) hJcM' hJcC hJcpc hcov
  have hTo : orderOf (⟨T, hTR⟩ : R) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact Subtype.ext hT2) fun h => hT1 (congrArg Subtype.val h)
  have h5 : 5 ∣ Nat.card ↥(centralizer ({T} : Set (Perm (Fin 42))) ⊓ S) := by
    have h1 := Subgroup.card_dvd_of_le himgT
    rw [himg60] at h1
    exact (Dvd.dvd.mul_right (by norm_num : 5 ∣ 60) k).trans h1
  rcases (orderOf_eq_two_iff ⟨T, hTR⟩).mp hTo with h1 | h2 | h3 | h4
  · obtain ⟨g, hg, he⟩ := eq_conj_of_isConj h1
    have he' : T = g * r₁ * g⁻¹ := he
    rw [he', card_centralizer_conj_inf_S hg] at h5
    have := card_C₁
    rw [C₁] at this
    rw [this] at h5
    omega
  · obtain ⟨g, hg, he⟩ := eq_conj_of_isConj h2
    have he' : T = g * r₂ * g⁻¹ := he
    rw [he', card_centralizer_conj_inf_S hg] at h5
    have := card_C₂
    rw [C₂] at this
    rw [this] at h5
    omega
  · obtain ⟨g, hg, he⟩ := eq_conj_of_isConj h3
    have he' : T = g * r₃ * g⁻¹ := he
    have hC60 : Nat.card ↥(centralizer ({T} : Set (Perm (Fin 42))) ⊓ S) = 60 := by
      rw [he', card_centralizer_conj_inf_S hg]
      exact card_C₃
    have hk1 : k = 1 := by
      have h1 := Subgroup.card_le_of_le himgT
      rw [himg60, hC60] at h1
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk
          exact absurd hk Nat.card_pos.ne'
        · exact h
      omega
    have himgeq : ρ.img Jc = centralizer ({T} : Set (Perm (Fin 42))) ⊓ S :=
      Subgroup.eq_of_le_of_card_ge himgT (by rw [himg60, hC60, hk1])
    have hUeq : Jc ⊓ UnbalancedLayer.coreActionKernel M = coreNOf Jc :=
      Subgroup.eq_of_le_of_card_ge hU (by rw [hk, hk1, mul_one])
    have hO1 : ∀ (z : X) (hz : z ∈ coreNOf Jc),
        ρ.φ ⟨z, hJcN (map_subtype_le _ hz)⟩ = 1 := by
      intro z hz
      have h1 : z ∈ Jc ⊓ UnbalancedLayer.coreActionKernel M := by
        rw [hUeq]
        exact hz
      exact (ρ.ker_iff _).2 (mem_inf.1 h1).2
    obtain ⟨j', hj'Jc, haj', -⟩ := hj
    set u : Perm (Fin 42) := g⁻¹ * r₄ * g with hudef
    have hu : u ∈ R := mul_mem (mul_mem (inv_mem hg) r₄_mem_R) hg
    have huc : IsConj (⟨u, hu⟩ : R) r₄R := by
      rw [isConj_iff]
      refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
      change g * u * g⁻¹ = r₄
      rw [hudef]
      group
    have hat' : r₄ * T = T * r₄ := by
      rw [← hρa, hTdef, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hat
    have hr₃ : r₃ = g⁻¹ * T * g := by
      rw [he']
      group
    have hur : u * r₃ = r₃ * u := by
      rw [hr₃, hudef]
      calc g⁻¹ * r₄ * g * (g⁻¹ * T * g) = g⁻¹ * (r₄ * T) * g := by group
        _ = g⁻¹ * (T * r₄) * g := by rw [hat']
        _ = g⁻¹ * T * g * (g⁻¹ * r₄ * g) := by group
    set s : Perm (Fin 42) := g⁻¹ * ρ.φ ⟨j', hJcN hj'Jc⟩ * g with hsdef
    have hjimg := himgT (ρ.phi_mem_img (g := ⟨j', hJcN hj'Jc⟩) hj'Jc)
    have hs : s ∈ C₃ := by
      obtain ⟨hjc, hjS⟩ := mem_inf.1 hjimg
      refine mem_inf.2 ⟨?_, ?_⟩
      · rw [mem_centralizer_singleton_iff] at hjc ⊢
        rw [hr₃, hsdef]
        calc g⁻¹ * ρ.φ ⟨j', hJcN hj'Jc⟩ * g * (g⁻¹ * T * g) =
            g⁻¹ * (ρ.φ ⟨j', hJcN hj'Jc⟩ * T) * g := by group
          _ = g⁻¹ * (T * ρ.φ ⟨j', hJcN hj'Jc⟩) * g := by rw [hjc]
          _ = g⁻¹ * T * g * (g⁻¹ * ρ.φ ⟨j', hJcN hj'Jc⟩ * g) := by group
      · have h1 := conj_mem_S (inv_mem hg) hjS
        rwa [inv_inv] at h1
    obtain ⟨x, hx, hne⟩ := graphUnitary_parts hu huc hur hs
    apply hne
    have hgx : g * x * g⁻¹ ∈ ρ.img Jc := by
      rw [himgeq]
      obtain ⟨hxc, hxS⟩ := mem_inf.1 hx
      refine mem_inf.2 ⟨?_, conj_mem_S hg hxS⟩
      rw [mem_centralizer_singleton_iff] at hxc ⊢
      rw [he']
      calc g * x * g⁻¹ * (g * r₃ * g⁻¹) = g * (x * r₃) * g⁻¹ := by group
        _ = g * (r₃ * x) * g⁻¹ := by rw [hxc]
        _ = g * r₃ * g⁻¹ * (g * x * g⁻¹) := by group
    obtain ⟨l, hlJc, hlx⟩ := ρ.mem_img.1 hgx
    have hw : j' * (l : X) * j'⁻¹ ∈ Jc := mul_mem (mul_mem hj'Jc hlJc) (inv_mem hj'Jc)
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem haj')).2 _ hw
    rw [inv_inv] at h1
    have h2 := hO1 _ h1
    have h3 : (⟨(j' * (l : X) * j'⁻¹)⁻¹ * (a * j'⁻¹) * (j' * (l : X) * j'⁻¹) * (a * j'⁻¹)⁻¹,
        hJcN (map_subtype_le _ h1)⟩ : ↥(normalizer (M : Set X))) =
        (⟨j', hJcN hj'Jc⟩ * l * (⟨j', hJcN hj'Jc⟩)⁻¹)⁻¹ * (⟨a, haM⟩ * l * (⟨a, haM⟩)⁻¹) :=
      Subtype.ext (by simp only [coe_mul, coe_inv]; group)
    rw [h3, map_mul, map_inv, inv_mul_eq_one] at h2
    have hkey : ρ.φ ⟨a, haM⟩ * ρ.φ l * (ρ.φ ⟨a, haM⟩)⁻¹ =
        ρ.φ ⟨j', hJcN hj'Jc⟩ * ρ.φ l * (ρ.φ ⟨j', hJcN hj'Jc⟩)⁻¹ := by
      simpa only [map_mul, map_inv] using h2.symm
    have hr4 : ρ.φ ⟨a, haM⟩ = g * u * g⁻¹ := by
      rw [hρa, hudef]
      group
    have hJ : ρ.φ ⟨j', hJcN hj'Jc⟩ = g * s * g⁻¹ := by
      rw [hsdef]
      group
    rw [hr4, hJ, hlx] at hkey
    have hu2 : u * u = 1 := by
      rw [hudef]
      calc g⁻¹ * r₄ * g * (g⁻¹ * r₄ * g) = g⁻¹ * (r₄ * r₄) * g := by group
        _ = 1 := by rw [GrSLit.L34Facts.r₄_mul_self]; group
    have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have h5 : u * x * u⁻¹ = s * x * s⁻¹ := by
      calc u * x * u⁻¹ = g⁻¹ * (g * u * g⁻¹ * (g * x * g⁻¹) * (g * u * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * (g * s * g⁻¹ * (g * x * g⁻¹) * (g * s * g⁻¹)⁻¹) * g := by rw [hkey]
        _ = s * x * s⁻¹ := by group
    rw [hu_inv] at h5
    calc u * x * u * s = s * x * s⁻¹ * s := by rw [h5]
      _ = s * x := by group
  · obtain ⟨g, hg, he⟩ := eq_conj_of_isConj h4
    have he' : T = g * r₄ * g⁻¹ := he
    rw [he', card_centralizer_conj_inf_S hg] at h5
    have := card_C₄
    rw [C₄] at this
    rw [this] at h5
    omega

end CFSG.ComponentClassification.SolMax
