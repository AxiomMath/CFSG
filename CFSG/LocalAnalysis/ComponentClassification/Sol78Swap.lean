module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78SwapBasic
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCaseB
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup UnbalancedLayer UnbalancedGS
open scoped Pointwise commutatorElement

section Diagonal

variable {Q : Type*} [Group Q]

@[expose] def diagonalHom (A B : Subgroup Q) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (g : Q)
    (hg : ∀ u ∈ A, g * u * g⁻¹ ∈ B) : A →* Q where
  toFun u := (u : Q) * (g * u * g⁻¹)
  map_one' := by simp
  map_mul' u v := by
    have h := hAB v v.2 _ (hg u u.2)
    simp only [Subgroup.coe_mul]
    calc (u : Q) * v * (g * (u * v) * g⁻¹) = u * (v * (g * u * g⁻¹)) * (g * v * g⁻¹) := by
          group
      _ = u * ((g * u * g⁻¹) * v) * (g * v * g⁻¹) := by rw [h]
      _ = u * (g * u * g⁻¹) * (v * (g * v * g⁻¹)) := by group

theorem diagonalHom_apply {A B : Subgroup Q} {hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a} {g : Q}
    {hg : ∀ u ∈ A, g * u * g⁻¹ ∈ B} (u : A) :
    diagonalHom A B hAB g hg u = (u : Q) * (g * u * g⁻¹) := rfl

theorem mem_center_of_diagonal_comm {A B : Subgroup Q} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {g : Q} (hg : ∀ u ∈ A, g * u * g⁻¹ ∈ B) {u : A}
    (hu : ∀ v ∈ A, (u : Q) * (g * u * g⁻¹) * v = v * ((u : Q) * (g * u * g⁻¹))) :
    u ∈ center A := by
  rw [mem_center_iff]
  intro v
  apply Subtype.ext
  have h1 := hu v v.2
  have h2 := hAB v v.2 _ (hg u u.2)
  simp only [Subgroup.coe_mul]
  have h3 : (u : Q) * v * (g * u * g⁻¹) = v * u * (g * u * g⁻¹) := by
    calc (u : Q) * v * (g * u * g⁻¹) = u * (v * (g * u * g⁻¹)) := by group
      _ = u * ((g * u * g⁻¹) * v) := by rw [h2]
      _ = u * (g * u * g⁻¹) * v := by group
      _ = v * (u * (g * u * g⁻¹)) := h1
      _ = v * u * (g * u * g⁻¹) := by group
  exact (mul_right_cancel h3).symm

theorem centralizes_of_comm_diagonal {A B : Subgroup Q} {g : Q} (hg : ∀ u ∈ A, g * u * g⁻¹ ∈ B)
    (hperf : ⁅A, A⁆ = A)
    (hD : ∀ d ∈ A ⊓ B, ∀ a ∈ A, d * a = a * d) {q : Q} (hqA : q ∈ normalizer (A : Set Q))
    (hqB : q ∈ normalizer (B : Set Q))
    (hq : ∀ u ∈ A, q * ((u : Q) * (g * u * g⁻¹)) * q⁻¹ = u * (g * u * g⁻¹)) :
    ∀ u ∈ A, q * u * q⁻¹ = u := by
  apply conj_eq_of_perfect hperf hqA
  intro u hu v hv
  have hw : g * u * g⁻¹ ∈ B := hg u hu
  have hqu : q * u * q⁻¹ ∈ A := (mem_normalizer_iff.mp hqA u).mp hu
  have hqw : q * (g * u * g⁻¹) * q⁻¹ ∈ B := (mem_normalizer_iff.mp hqB _).mp hw
  have heq := hq u hu
  have hc : u⁻¹ * (q * u * q⁻¹) = (g * u * g⁻¹) * (q * (g * u * g⁻¹) * q⁻¹)⁻¹ := by
    calc u⁻¹ * (q * u * q⁻¹) = u⁻¹ * (q * (u * (g * u * g⁻¹)) * q⁻¹) *
          (q * (g * u * g⁻¹) * q⁻¹)⁻¹ := by group
      _ = u⁻¹ * (u * (g * u * g⁻¹)) * (q * (g * u * g⁻¹) * q⁻¹)⁻¹ := by rw [heq]
      _ = (g * u * g⁻¹) * (q * (g * u * g⁻¹) * q⁻¹)⁻¹ := by group
  have hmem : u⁻¹ * (q * u * q⁻¹) ∈ A ⊓ B :=
    mem_inf.mpr ⟨mul_mem (inv_mem hu) hqu, hc ▸ mul_mem hw (inv_mem hqw)⟩
  exact hD _ hmem v hv

end Diagonal

section Perm

variable {G : Type*} [Group G]

theorem conjugate_conjugate (M : Subgroup G) (a b : G) :
    conjugate (conjugate M a) b = conjugate M (a * b) := by
  unfold conjugate
  rw [Subgroup.map_map]
  congr 1
  ext g
  simp [mul_inv_rev, mul_assoc]

theorem card_le_two_mul_card_inf_normalizer [Finite G] {Q M M' : Subgroup G}
    (hperm : ∀ q ∈ Q, conjugate M q = M ∨ conjugate M q = M') :
    Nat.card Q ≤ 2 * Nat.card (Q ⊓ normalizer (M : Set G) : Subgroup G) := by
  classical
  by_cases h : ∃ q₀ ∈ Q, conjugate M q₀ ≠ M
  · obtain ⟨q₀, hq₀, hq₀M⟩ := h
    have hq₀M' : conjugate M q₀ = M' := (hperm q₀ hq₀).resolve_left hq₀M
    have hmem : ∀ q ∈ Q, conjugate M q ≠ M → q * q₀⁻¹ ∈ Q ⊓ normalizer (M : Set G) := by
      intro q hq hqM
      have hqM' : conjugate M q = M' := (hperm q hq).resolve_left hqM
      refine mem_inf.mpr ⟨mul_mem hq (inv_mem hq₀), mem_normalizer_of_conjugate_eq ?_⟩
      rw [← conjugate_conjugate, hqM', ← hq₀M', conjugate_conjugate, mul_inv_cancel]
      ext g
      simp [conjugate]
    let f : Q → (Q ⊓ normalizer (M : Set G) : Subgroup G) × Bool := fun q =>
      if hq : conjugate M q = M then
        (⟨q, mem_inf.mpr ⟨q.2, mem_normalizer_of_conjugate_eq hq⟩⟩, false)
      else (⟨q * q₀⁻¹, hmem q q.2 hq⟩, true)
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      split_ifs at hab with ha hb hb
      · exact Subtype.ext (congrArg (fun p => ((p.1 : _) : G)) hab)
      · exact absurd (congrArg Prod.snd hab) (by simp)
      · exact absurd (congrArg Prod.snd hab) (by simp)
      · have h1 : (a : G) * q₀⁻¹ = b * q₀⁻¹ := congrArg (fun p => ((p.1 : _) : G)) hab
        exact Subtype.ext (mul_right_cancel h1)
    calc Nat.card Q ≤ Nat.card ((Q ⊓ normalizer (M : Set G) : Subgroup G) × Bool) :=
          Nat.card_le_card_of_injective f hf
      _ = 2 * Nat.card (Q ⊓ normalizer (M : Set G) : Subgroup G) := by
          rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]
  · push Not at h
    have hle : Q ≤ Q ⊓ normalizer (M : Set G) := fun q hq =>
      mem_inf.mpr ⟨hq, mem_normalizer_of_conjugate_eq (h q hq)⟩
    have := Subgroup.card_le_of_le hle
    omega

end Perm

section Swap

variable {X : Type} [Group X] [Finite X]

theorem exists_not_mem_center_of_nonabelian {Q : Type*} [Group Q] {a b : Q} (hab : a * b ≠ b * a) :
    ∃ r : Q, r ∉ center Q := ⟨a, fun h => hab ((mem_center_iff.mp h) b).symm⟩

theorem swap_pump_up (hSchur : SolAltLit.SchurAlternatingMultiplierInput) {x y : X}
    {L M Q : Subgroup X} {m : ℕ} (hP : IsDoublePair x L m) (hy : orderOf y = 2)
    (hTxy : gsFixedLayer L y ≤ centralizer ({x} : Set X) ⊓ centralizer ({y} : Set X))
    (hcore : (pPrimeCore 2 (gsFixedLayer L y)).map (gsFixedLayer L y).subtype =
      gsFixedLayer L y ⊓ (pPrimeCore 2 L).map L.subtype)
    (φ : gsFixedLayer L y ⧸ pPrimeCore 2 (gsFixedLayer L y) ≃* L ⧸ pPrimeCore 2 L)
    (hyT : y ∈ gsFixedLayer L y) (hMy : M ≤ centralizer ({y} : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({y} : Set X))))
    (hTM : gsFixedLayer L y ≤ M ⊔ conjugate M x)
    (hTMpc : IsPComponent 2 ((gsFixedLayer L y).subgroupOf
      ((M ⊔ conjugate M x) ⊓ centralizer ({x} : Set X))))
    (hMx : conjugate M x ≠ M) (hQ : IsPGroup 2 Q) (hQx : Q ≤ centralizer ({x} : Set X))
    (hQL : Q ≤ coreActionKernel L) (hQy : Q ≤ centralizer ({y} : Set X)) :
    IsDoublePair y M m ∧ ∃ P : Subgroup X, IsPGroup 2 P ∧
      P ≤ centralizer ({y} : Set X) ⊓ coreActionKernel M ∧ Nat.card Q < Nat.card P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hqL, hZL2, ⟨eLbar⟩⟩ := hP.coreQuotient hSchur
  obtain ⟨hx, hLx, hL, hmo, hm7, -, ⟨eL⟩⟩ := hP
  set T := gsFixedLayer L y with hTdef
  set Hb := centralizer ({y} : Set X) with hHb
  set Cx := centralizer ({x} : Set X) with hCx
  have hTHb : T ≤ Hb := hTxy.trans inf_le_right
  have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp (hTxy hyT).1).symm
  have hxHb : x ∈ Hb := mem_centralizer_singleton_iff.mpr hxy
  set x' : Hb := ⟨x, hxHb⟩ with hx'def
  have hx'o : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  have hx'2 : x' * x' = 1 := by rw [← pow_two, ← hx'o, pow_orderOf_eq_one]
  have hx'inv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
  have hyHb : y ∈ Hb := mem_centralizer_singleton_iff.mpr rfl
  set y' : Hb := ⟨y, hyHb⟩ with hy'def
  obtain ⟨hMaHb, -⟩ := UGSChain.conjugate_isPComponent_centralizer (b := y) hxy hMy hM
  set M₁ : Subgroup Hb := M.subgroupOf Hb with hM₁
  set M₂ : Subgroup Hb := conjugate M₁ x' with hM₂
  have hM₂eq : M₂ = (conjugate M x).subgroupOf Hb := conjugate_subgroupOf_eq M Hb x'
  have hM₁₂ : M₁ ⊔ M₂ = (M ⊔ conjugate M x).subgroupOf Hb := by
    rw [hM₂eq, subgroupOf_sup hMy hMaHb]
  have hne : M₁ ≠ M₂ := by
    intro h
    apply hMx
    rw [hM₂eq, hM₁, subgroupOf_inj, inf_of_le_left hMy, inf_of_le_left hMaHb] at h
    exact h.symm
  set T' : Subgroup Hb := T.subgroupOf Hb with hT'
  have hcenx : centralizer ({x'} : Set Hb) = (Cx ⊓ Hb).subgroupOf Hb := by
    ext w
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨congrArg Subtype.val h, w.2⟩, fun h => Subtype.ext h.1⟩
  have hKHb : M ⊔ conjugate M x ≤ Hb := sup_le hMy hMaHb
  have hCK : (M₁ ⊔ M₂) ⊓ centralizer ({x'} : Set Hb) =
      ((M ⊔ conjugate M x) ⊓ Cx).subgroupOf Hb := by
    rw [hM₁₂, hcenx]
    ext w
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, w.2⟩⟩
  have hT'C : T' ≤ (M₁ ⊔ M₂) ⊓ centralizer ({x'} : Set Hb) := by
    rw [hCK]
    intro w hw
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hTM (mem_subgroupOf.mp hw),
      (hTxy (mem_subgroupOf.mp hw)).1⟩)
  have hT'pc : IsPComponent 2 (T'.subgroupOf ((M₁ ⊔ M₂) ⊓ centralizer ({x'} : Set Hb))) := by
    rw [hCK, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left.trans hKHb) 2 Nat.prime_two]
    exact hTMpc
  obtain ⟨-, hlayer⟩ := OrbitFixedComponent.swap_case hx'o M₁ hM hne T' hT'C hT'pc
  have hT₀ : T' = gsFixedLayer (M₁ ⊔ M₂) x' := hlayer.symm
  have hM₂comp : IsPComponent 2 M₂ := isPComponent_conjugate hM x'
  have hM₂map : M₂ = M₁.map (MulAut.conj x').toMonoidHom := by
    rw [hM₂]
    unfold conjugate
    rw [hx'inv]
  set N := pPrimeCore 2 Hb with hN
  set π := QuotientGroup.mk' N with hπ
  set A : Subgroup (Hb ⧸ N) := M₁.map π with hA
  set B : Subgroup (Hb ⧸ N) := M₂.map π with hB
  set R : Subgroup (Hb ⧸ N) := T'.map π with hR
  obtain ⟨α, hαapp, -, hcommAB, hAq, -, hDcent, -, hRmem, ⟨e, he⟩, -⟩ :=
    UnbalancingLocal.Correspondence.swap_layer_analysis hM hM₂comp hne hx'2 hM₂map A B rfl rfl
      T' hT₀
  set g := π x' with hg
  have hgAB : ∀ u ∈ A, g * u * g⁻¹ ∈ B := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨x' * u * x'⁻¹, ?_, by rw [hg, map_mul, map_mul, map_inv]⟩
    rw [hM₂map]
    exact ⟨u, hu, rfl⟩
  set δ := diagonalHom A B hcommAB g hgAB with hδ
  have hδR : ∀ u : A, δ u ∈ R := by
    intro u
    rw [hRmem]
    refine ⟨⟨u, mem_sup_left u.2⟩, u.2, ?_⟩
    rw [hδ, diagonalHom_apply, Subgroup.coe_mul, hαapp]
    rfl
  have hδsurj : ∀ r ∈ R, ∃ u : A, δ u = r := by
    intro r hr
    obtain ⟨k, hkA, rfl⟩ := (hRmem r).mp hr
    refine ⟨⟨k, hkA⟩, ?_⟩
    rw [hδ, diagonalHom_apply, Subgroup.coe_mul, hαapp]
    rfl
  let δR : A →* R := δ.codRestrict R hδR
  have hδRs : Function.Surjective δR := by
    rintro ⟨r, hr⟩
    obtain ⟨u, hu⟩ := hδsurj r hr
    exact ⟨u, Subtype.ext hu⟩
  let eR : R ≃* L ⧸ pPrimeCore 2 L :=
    e.symm.trans ((coreQuotCongr (subgroupOfEquivOfLe hTHb)).trans φ)
  have hRnc : ∃ r : R, r ∉ center R := by
    obtain ⟨a, b, hab⟩ := hqL.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine exists_not_mem_center_of_nonabelian (a := eR.symm a) (b := eR.symm b) ?_
    intro h
    apply hab
    have h1 := congrArg eR h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
  obtain ⟨eAR⟩ := nonempty_centralQuot_equiv_of_surjective hAq δR hδRs hRnc
  have hM₁sub : M₁.IsSubnormal := by
    obtain ⟨_, _, h, _, _⟩ := hM
    exact h
  let eM₁A : M₁ ⧸ pPrimeCore 2 M₁ ≃* A :=
    CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage 2 M₁ hM₁sub
  let eMA : M ⧸ pPrimeCore 2 M ≃* A :=
    (coreQuotCongr (subgroupOfEquivOfLe hMy).symm).trans eM₁A
  let eMalt : M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin m) :=
    (coreQuotientCenterEquiv M).symm.trans ((centerQuotCongr eMA).trans (eAR.trans
      ((centerQuotCongr eR).trans ((coreQuotientCenterEquiv L).trans eL))))
  have hy'T : y' ∈ T' := hyT
  have hπy : π y' ∈ R := mem_map_of_mem π hy'T
  have hπy1 : π y' ≠ 1 := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have h2 := N.orderOf_dvd_natCard h
    rw [hy'def, Subgroup.orderOf_mk, hy] at h2
    exact absurd (Nat.Coprime.eq_one_of_dvd (pPrimeCore_coprime_card (p := 2) (G := Hb)) h2)
      (by norm_num)
  have hπyc : ∀ w : Hb ⧸ N, π y' * w = w * π y' := by
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp w.2).symm
  obtain ⟨u₀, hu₀⟩ := hδsurj _ hπy
  have hu₀Z : u₀ ∈ center A := by
    apply mem_center_of_diagonal_comm hcommAB hgAB
    intro v _
    have h := hπyc v
    rw [← hu₀, hδ, diagonalHom_apply] at h
    exact h
  have hu₀1 : u₀ ≠ 1 := by
    intro h
    apply hπy1
    rw [← hu₀, h, map_one]
  have hZA : center A ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at hu₀Z
    exact hu₀1 hu₀Z
  have hZM : center (M ⧸ pPrimeCore 2 M) ≠ ⊥ := by
    intro h
    apply hZA
    rw [← map_center_eq_of_mulEquiv eMA, h, Subgroup.map_bot]
  have hMne : Open.fusionZStar M ≠ pPrimeCore 2 M := fun h => hZM ((fusionZStar_eq_iff M).mp h)
  have hPair : IsDoublePair y M m := ⟨hy, hMy, hM, hmo, hm7, hMne, ⟨eMalt⟩⟩
  refine ⟨hPair, ?_⟩
  have hQR : ∀ q (hq : q ∈ Q), ∀ t ∈ T', π (⟨q, hQy hq⟩ : Hb) * π t = π t * π ⟨q, hQy hq⟩ := by
    intro q hq t ht
    set q' : Hb := ⟨q, hQy hq⟩ with hq'
    have htT : (t : X) ∈ T := ht
    have hqT : q ∈ normalizer (T : Set X) :=
      TBLit.mem_normalizer_gsFixedLayer (hQL hq).1 (mem_centralizer_singleton_iff.mp (hQy hq))
    set w : Hb := t⁻¹ * q'⁻¹ * t * q' with hw
    have hwL : (w : X) ∈ (pPrimeCore 2 L).map L.subtype := by
      have h := (hQL hq).2 (t : X) (mem_inf.mp (gsFixedLayer_le_inf L y htT)).1
      simpa [hw, hq'] using h
    have hwT : (w : X) ∈ T := by
      have h1 : q⁻¹ * (t : X) * q ∈ T := by
        have := (mem_normalizer_iff.mp (inv_mem hqT) t).mp htT
        simpa using this
      have : (w : X) = (t : X)⁻¹ * (q⁻¹ * t * q) := by simp [hw, hq', mul_assoc]
      rw [this]
      exact mul_mem (inv_mem htT) h1
    have hwO : (w : X) ∈ (pPrimeCore 2 T).map T.subtype := by
      rw [hcore]
      exact mem_inf.mpr ⟨hwT, hwL⟩
    have hwT' : w ∈ T' := hwT
    have hwO' : (⟨w, hwT'⟩ : T') ∈ pPrimeCore 2 T' := by
      obtain ⟨w₀, hw₀, hw₀w⟩ := hwO
      have h1 := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hTHb).symm
      rw [← h1]
      refine ⟨w₀, hw₀, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simpa using hw₀w
    have hπw : π w = 1 := by
      have h1 := he ⟨w, hwT'⟩
      have h2 : ((⟨w, hwT'⟩ : T') : T' ⧸ pPrimeCore 2 T') = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hwO'
      rw [h2, map_one] at h1
      have h4 : ((w : Hb) : Hb ⧸ N) = 1 := by
        have h5 : ((1 : R) : Hb ⧸ N) = 1 := rfl
        rw [← h5]
        exact h1.symm
      exact h4
    have h3 : (π t)⁻¹ * (π q')⁻¹ * π t * π q' = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact hπw
    calc π q' * π t = π t * π q' * ((π t)⁻¹ * (π q')⁻¹ * π t * π q')⁻¹ := by group
      _ = π t * π q' := by rw [h3, inv_one, mul_one]
  have hperm : ∀ q ∈ Q, conjugate M q = M ∨ conjugate M q = conjugate M x := by
    intro q hq
    set q' : Hb := ⟨q, hQy hq⟩ with hq'
    have hqx' : q' * x' = x' * q' := Subtype.ext (mem_centralizer_singleton_iff.mp (hQx hq))
    have hqT : q ∈ normalizer (T : Set X) :=
      TBLit.mem_normalizer_gsFixedLayer (hQL hq).1 (mem_centralizer_singleton_iff.mp (hQy hq))
    set M₃ := conjugate M₁ q' with hM₃
    set M₄ := conjugate M₂ q' with hM₄
    have hM₄eq : M₄ = conjugate M₃ x' := by
      rw [hM₄, hM₃, hM₂, conjugate_conjugate, conjugate_conjugate, hqx']
    have hT'34 : T' ≤ M₃ ⊔ M₄ := by
      intro t ht
      have htT : (t : X) ∈ T := ht
      have h1 : q * (t : X) * q⁻¹ ∈ T := (mem_normalizer_iff.mp hqT t).mp htT
      have h1' : q' * t * q'⁻¹ ∈ T' := h1
      have h2 : q' * t * q'⁻¹ ∈ M₁ ⊔ M₂ := (hT'C.trans inf_le_left) h1'
      have h3 : t ∈ conjugate (M₁ ⊔ M₂) q' := by
        rw [mem_conjugate_iff]
        exact h2
      unfold conjugate at h3
      rwa [Subgroup.map_sup] at h3
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hM₃X : M₃ = (conjugate M q).subgroupOf Hb := conjugate_subgroupOf_eq M Hb q'
    obtain ⟨hMqHb, -⟩ := UGSChain.conjugate_isPComponent_centralizer (b := y)
      (mem_centralizer_singleton_iff.mp (hQy hq)) hMy hM
    have h31 : M₃ ≠ M₁ := by
      intro h
      apply hc1
      rw [hM₃X, hM₁, subgroupOf_inj, inf_of_le_left hMqHb, inf_of_le_left hMy] at h
      exact h
    have h32 : M₃ ≠ M₂ := by
      intro h
      apply hc2
      rw [hM₃X, hM₂eq, subgroupOf_inj, inf_of_le_left hMqHb, inf_of_le_left hMaHb] at h
      exact h
    have hx'x' : ∀ K : Subgroup Hb, conjugate (conjugate K x') x' = K := by
      intro K
      rw [conjugate_conjugate, hx'2]
      ext w
      simp [conjugate]
    have h41 : M₄ ≠ M₁ := by
      intro h
      apply h32
      rw [← hx'x' M₃, ← hM₄eq, h, hM₂]
    have h42 : M₄ ≠ M₂ := by
      intro h
      apply h31
      rw [← hx'x' M₃, ← hM₄eq, h, hM₂, hx'x']
    have hM₃c : IsPComponent 2 M₃ := isPComponent_conjugate hM q'
    have hM₄c : IsPComponent 2 M₄ := isPComponent_conjugate hM₂comp q'
    obtain ⟨-, -, -, h31c⟩ := UnbalancingLocal.Correspondence.image_components hM₃c hM h31
    obtain ⟨-, -, -, h32c⟩ :=
      UnbalancingLocal.Correspondence.image_components hM₃c hM₂comp h32
    obtain ⟨-, -, -, h41c⟩ := UnbalancingLocal.Correspondence.image_components hM₄c hM h41
    obtain ⟨-, -, -, h42c⟩ :=
      UnbalancingLocal.Correspondence.image_components hM₄c hM₂comp h42
    have hcomm : ∀ s ∈ A ⊔ B, ∀ r ∈ (M₃ ⊔ M₄).map π, r * s = s * r := by
      intro s hs
      have hle : (M₃ ⊔ M₄).map π ≤ centralizer ({s} : Set (Hb ⧸ N)) := by
        rw [Subgroup.map_sup]
        refine sup_le (fun r hr => ?_) (fun r hr => ?_)
        · have hAB : A ⊔ B ≤ centralizer ({r} : Set (Hb ⧸ N)) := sup_le
            (fun a ha => mem_centralizer_singleton_iff.mpr (h31c r hr a ha).symm)
            (fun b hb => mem_centralizer_singleton_iff.mpr (h32c r hr b hb).symm)
          exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hAB hs)).symm
        · have hAB : A ⊔ B ≤ centralizer ({r} : Set (Hb ⧸ N)) := sup_le
            (fun a ha => mem_centralizer_singleton_iff.mpr (h41c r hr a ha).symm)
            (fun b hb => mem_centralizer_singleton_iff.mpr (h42c r hr b hb).symm)
          exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hAB hs)).symm
      intro r hr
      exact mem_centralizer_singleton_iff.mp (hle hr)
    obtain ⟨⟨r, hr⟩, hrZ⟩ := hRnc
    apply hrZ
    rw [mem_center_iff]
    rintro ⟨s, hs⟩
    apply Subtype.ext
    have hr34 : r ∈ (M₃ ⊔ M₄).map π := map_mono hT'34 hr
    have hsAB : s ∈ A ⊔ B := by
      have : T'.map π ≤ (M₁ ⊔ M₂).map π := map_mono (hT'C.trans inf_le_left)
      rw [Subgroup.map_sup] at this
      exact this hs
    exact (hcomm s hsAB r hr34).symm
  set Q₁ := Q ⊓ normalizer (M : Set X) with hQ₁
  have hQcard : Nat.card Q ≤ 2 * Nat.card Q₁ := card_le_two_mul_card_inf_normalizer hperm
  have hQ₁2 : IsPGroup 2 Q₁ := hQ.to_inf_left
  have hnorm₁ : ∀ q (hq : q ∈ Q₁), (⟨q, hQy (mem_inf.mp hq).1⟩ : Hb) ∈
      normalizer (M₁ : Set Hb) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro w
    have h := (mem_normalizer_iff.mp (mem_inf.mp hq).2) w
    simpa [hM₁, mem_subgroupOf] using h
  have hqxN : ∀ q (hq : q ∈ Q₁), q ∈ normalizer (conjugate M x : Set X) := by
    intro q hq
    have hqx : q * x = x * q := mem_centralizer_singleton_iff.mp (hQx (mem_inf.mp hq).1)
    have hqM : q ∈ normalizer (M : Set X) := (mem_inf.mp hq).2
    rw [mem_normalizer_iff]
    intro w
    rw [mem_conjugate_iff, mem_conjugate_iff]
    have h1 : x * (q * w * q⁻¹) * x⁻¹ = q * (x * w * x⁻¹) * q⁻¹ := by
      have hx' : x * q = q * x := hqx.symm
      calc x * (q * w * q⁻¹) * x⁻¹ = (x * q) * w * (x * q)⁻¹ := by group
        _ = (q * x) * w * (q * x)⁻¹ := by rw [hx']
        _ = q * (x * w * x⁻¹) * q⁻¹ := by group
    rw [h1]
    exact mem_normalizer_iff.mp hqM _
  have hnorm₂ : ∀ q (hq : q ∈ Q₁), (⟨q, hQy (mem_inf.mp hq).1⟩ : Hb) ∈
      normalizer (M₂ : Set Hb) := by
    intro q hq
    rw [hM₂eq, mem_normalizer_iff]
    intro w
    have h := (mem_normalizer_iff.mp (hqxN q hq)) w
    simpa [mem_subgroupOf] using h
  have hmapN : ∀ {K : Subgroup Hb} {h : Hb}, h ∈ normalizer (K : Set Hb) →
      π h ∈ normalizer ((K.map π : Subgroup (Hb ⧸ N)) : Set (Hb ⧸ N)) := by
    intro K h hh
    rw [mem_normalizer_iff_map_conj_eq] at hh ⊢
    have hcomp : ((MulAut.conj (π h) : Hb ⧸ N →* Hb ⧸ N)).comp π =
        π.comp (MulAut.conj h : Hb →* Hb) := by
      ext w
      simp [MulAut.conj_apply]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hh]
  have hperfA : ⁅A, A⁆ = A := by
    have : Group.IsPerfect A := hAq.1
    exact Subgroup.commutator_eq_self
  have hDA : ∀ d ∈ A ⊓ B, ∀ a ∈ A, d * a = a * d :=
    fun d hd a ha => hDcent d hd a (mem_sup_left ha)
  have hQ₁A : ∀ q (hq : q ∈ Q₁), ∀ u ∈ A,
      π (⟨q, hQy (mem_inf.mp hq).1⟩ : Hb) * u * (π ⟨q, hQy (mem_inf.mp hq).1⟩)⁻¹ = u := by
    intro q hq
    apply centralizes_of_comm_diagonal hgAB hperfA hDA (hmapN (hnorm₁ q hq))
      (hmapN (hnorm₂ q hq))
    intro u hu
    obtain ⟨t, ht, htu⟩ := (show (u : Hb ⧸ N) * (g * u * g⁻¹) ∈ R from
      hδR ⟨u, hu⟩)
    have h1 := hQR q (mem_inf.mp hq).1 t ht
    rw [← htu]
    calc π ⟨q, _⟩ * π t * (π ⟨q, _⟩)⁻¹ = π t * π ⟨q, _⟩ * (π ⟨q, _⟩)⁻¹ := by rw [h1]
      _ = π t := by group
  have hQ₁K : Q₁ ≤ Hb ⊓ coreActionKernel M := by
    intro q hq
    refine mem_inf.mpr ⟨hQy (mem_inf.mp hq).1, ?_⟩
    set q' : Hb := ⟨q, hQy (mem_inf.mp hq).1⟩ with hq'
    have hq'K : q' ∈ coreActionKernel M₁ := by
      refine ⟨hnorm₁ q hq, fun j hj => ?_⟩
      have hjq : j⁻¹ * q'⁻¹ * j * q' ∈ M₁ := by
        have h1 : q'⁻¹ * j * q' ∈ M₁ := by
          have := (mem_normalizer_iff.mp (inv_mem (hnorm₁ q hq)) j).mp hj
          simpa using this
        have : j⁻¹ * q'⁻¹ * j * q' = j⁻¹ * (q'⁻¹ * j * q') := by group
        rw [this]
        exact mul_mem (inv_mem hj) h1
      have hπ1 : π (j⁻¹ * q'⁻¹ * j * q') = 1 := by
        have h2 := hQ₁A q hq (π j) (mem_map_of_mem π hj)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        calc (π j)⁻¹ * (π q')⁻¹ * π j * π q' =
            (π j)⁻¹ * ((π q')⁻¹ * (π q' * π j * (π q')⁻¹) * π q') := by rw [h2]; group
          _ = 1 := by group
      have hN' : j⁻¹ * q'⁻¹ * j * q' ∈ M₁ ⊓ N := by
        refine mem_inf.mpr ⟨hjq, ?_⟩
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπ1
      rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hM₁sub]
      exact hN'
    exact mem_coreActionKernel_of_subgroupOf hMy hq'K
  have hMxK : conjugate M x ≤ Hb ⊓ coreActionKernel M := by
    obtain ⟨-, hdist⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
      Nat.prime_two M₁ M₂ hM hM₂comp
    obtain ⟨hM₂N, -, hcomm₁₂, -⟩ := hdist hne
    intro w hw
    have hwHb : w ∈ Hb := hMaHb hw
    refine mem_inf.mpr ⟨hwHb, ?_⟩
    have hw' : (⟨w, hwHb⟩ : Hb) ∈ M₂ := by rw [hM₂eq]; exact hw
    have hwK : (⟨w, hwHb⟩ : Hb) ∈ coreActionKernel M₁ := by
      refine ⟨hM₂N hw', fun j hj => ?_⟩
      have h1 := commutator_mem_commutator (inv_mem hj) (inv_mem hw')
      have h2 := (hcomm₁₂ h1)
      rw [commutatorElement_def, inv_inv, inv_inv] at h2
      exact (mem_inf.mp h2).1
    exact mem_coreActionKernel_of_subgroupOf hMy hwK
  have hAB' : A.map (MulAut.conj g).toMonoidHom = B := by
    rw [hB, hM₂map, hA, Subgroup.map_map, Subgroup.map_map]
    congr 1
  let eAB : A ≃* B :=
    ((MulAut.conj g).subgroupMap A).trans (MulEquiv.subgroupCongr hAB')
  obtain ⟨-, -, hZM2, -⟩ := hPair.coreQuotient hSchur
  have hZB : Nat.card (center B) = 2 := by
    rw [← map_center_eq_of_mulEquiv eAB, Subgroup.card_map_of_injective eAB.injective,
      ← map_center_eq_of_mulEquiv eMA, Subgroup.card_map_of_injective eMA.injective, hZM2]
  have hodd2 : ∀ w ∈ Q, w ∈ (N.map Hb.subtype : Subgroup X) → w = 1 := by
    intro w hwQ hwN
    obtain ⟨k, hk⟩ := hQ ⟨w, hwQ⟩
    have h1 : orderOf w ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨w', hw', rfl⟩ := hwN
    have h2 := N.orderOf_dvd_natCard hw'
    rw [Hb.subtype_apply, Subgroup.orderOf_coe] at h1
    have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
      Nat.Coprime.pow_left k (pPrimeCore_coprime_card (p := 2) (G := Hb))
    have h3 : orderOf w' = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff] at h3
    rw [h3]
    rfl
  have hIcard : Nat.card (Q₁ ⊓ conjugate M x : Subgroup X) ≤ 2 := by
    rw [← hZB]
    let ψ : (Q₁ ⊓ conjugate M x : Subgroup X) → center B := fun q =>
      ⟨⟨π ⟨q, hMaHb (mem_inf.mp q.2).2⟩, by
        rw [hB]
        refine mem_map_of_mem π ?_
        rw [hM₂eq]
        exact (mem_inf.mp q.2).2⟩, by
        rw [mem_center_iff]
        rintro ⟨b, hb⟩
        apply Subtype.ext
        change b * π ⟨q, _⟩ = π ⟨q, _⟩ * b
        have hqQ : (q : X) ∈ Q := (mem_inf.mp (mem_inf.mp q.2).1).1
        have hqB : π ⟨q, hMaHb (mem_inf.mp q.2).2⟩ ∈ B := by
          rw [hB]
          refine mem_map_of_mem π ?_
          rw [hM₂eq]
          exact (mem_inf.mp q.2).2
        rw [← hAB'] at hb
        obtain ⟨u, hu, rfl⟩ := hb
        change g * u * g⁻¹ * _ = _ * (g * u * g⁻¹)
        obtain ⟨t, ht, htu⟩ := (show (u : Hb ⧸ N) * (g * u * g⁻¹) ∈ R from hδR ⟨u, hu⟩)
        have h1 := hQR q hqQ t ht
        rw [htu] at h1
        have hq'eq : (⟨(q : X), hQy hqQ⟩ : Hb) = ⟨q, hMaHb (mem_inf.mp q.2).2⟩ := rfl
        rw [hq'eq] at h1
        have h2 := hcommAB u hu _ hqB
        set c := π ⟨q, hMaHb (mem_inf.mp q.2).2⟩
        calc g * u * g⁻¹ * c = u⁻¹ * (u * (g * u * g⁻¹)) * c := by group
          _ = u⁻¹ * (c * (u * (g * u * g⁻¹))) := by rw [mul_assoc, ← h1]
          _ = u⁻¹ * (c * u) * (g * u * g⁻¹) := by group
          _ = u⁻¹ * (u * c) * (g * u * g⁻¹) := by rw [h2]
          _ = c * (g * u * g⁻¹) := by group⟩
    have hψ : Function.Injective ψ := by
      intro q₁ q₂ h
      have h1 : π ⟨q₁, hMaHb (mem_inf.mp q₁.2).2⟩ = π ⟨q₂, hMaHb (mem_inf.mp q₂.2).2⟩ :=
        congrArg (fun z : center B => ((z : B) : Hb ⧸ N)) h
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      have hmem : (q₁ : X)⁻¹ * q₂ ∈ (N.map Hb.subtype : Subgroup X) := ⟨_, h1, rfl⟩
      have hQmem : (q₁ : X)⁻¹ * q₂ ∈ Q :=
        mul_mem (inv_mem (mem_inf.mp (mem_inf.mp q₁.2).1).1) (mem_inf.mp (mem_inf.mp q₂.2).1).1
      have := hodd2 _ hQmem hmem
      apply Subtype.ext
      calc (q₁ : X) = q₁ * ((q₁ : X)⁻¹ * q₂) := by rw [this, mul_one]
        _ = q₂ := by group
    exact Nat.card_le_card_of_injective ψ hψ
  have hI2 : Nat.card (Q₁ ⊓ conjugate M x : Subgroup X) ∣ 2 := by
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp (hQ₁2.to_inf_left (K := conjugate M x))
    rw [hb] at hIcard ⊢
    have : b ≤ 1 := by
      by_contra h
      have : 2 ^ 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases b <;> norm_num
  have h16 : 16 ∣ Nat.card (conjugate M x) := by
    obtain ⟨-, -, -, ⟨eMbar⟩⟩ := hPair.coreQuotient hSchur
    have h1 : Nat.card (conjugate M x) = Nat.card M := by
      unfold conjugate
      exact Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 M)
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (M ⧸ pPrimeCore 2 M))
    rw [hZM2, Nat.card_congr eMbar.toEquiv] at h3
    have h4 : 2 * Nat.card (alternatingGroup (Fin m)) = m.factorial := by
      have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have h5 : 16 ∣ m.factorial :=
      dvd_trans (by decide : 16 ∣ (6 : ℕ).factorial) (Nat.factorial_dvd_factorial (by omega))
    rw [h1, h2, h3]
    rw [← h4] at h5
    exact dvd_mul_of_dvd_left (by rw [mul_comm]; exact h5) _
  set W := Q₁ ⊔ conjugate M x with hW
  have hWK : W ≤ Hb ⊓ coreActionKernel M := sup_le hQ₁K hMxK
  have hprod := card_sup_mul_card_inf' (hqxN · ·)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hQ₁2
  have hWdvd : 2 ^ (a + 3) ∣ Nat.card W := by
    have h1 : 2 ^ (a + 4) ∣ Nat.card W * Nat.card (Q₁ ⊓ conjugate M x : Subgroup X) := by
      rw [hprod, ha, pow_add]
      exact mul_dvd_mul_left _ h16
    have h2 : Nat.card W * Nat.card (Q₁ ⊓ conjugate M x : Subgroup X) ∣ Nat.card W * 2 :=
      mul_dvd_mul_left _ hI2
    have h3 : 2 * 2 ^ (a + 3) ∣ 2 * Nat.card W := by
      rw [← pow_succ', mul_comm 2 (Nat.card W)]
      exact dvd_trans h1 h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  obtain ⟨S⟩ : Nonempty (Sylow 2 W) := inferInstance
  refine ⟨(S : Subgroup W).map W.subtype, S.isPGroup'.map W.subtype,
    (map_subtype_le _).trans hWK, ?_⟩
  rw [Subgroup.card_map_of_injective W.subtype_injective]
  have hS := S.pow_dvd_card_of_pow_dvd_card hWdvd
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hSle := Nat.le_of_dvd hSpos hS
  have : Nat.card Q ≤ 2 * 2 ^ a := ha ▸ hQcard
  calc Nat.card Q ≤ 2 * 2 ^ a := this
    _ < 2 ^ (a + 3) := by rw [pow_add]; nlinarith [Nat.one_le_two_pow (n := a)]
    _ ≤ Nat.card S := hSle

end Swap

end CFSG.ComponentClassification.Sol78
