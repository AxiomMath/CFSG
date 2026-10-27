module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4LocalCore
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4PlaneCentralizer
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4InSituNormalizer
public import CFSG.HardMathSupport.Malle.Proving.ReeF4NormalizerPlane
public import CFSG.RankThree.PartOne.SEITZ12.TConj
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Local
public import CFSG.RankThree.PartOne.SEITZ12.Defs

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

section Generic

variable {G : Type*} [Group G]

lemma card_normalizer_subgroupOf (A T : Subgroup G) (h : T ≤ A) :
    Nat.card (Subgroup.normalizer ((T.subgroupOf A : Subgroup A) : Set A)) =
      Nat.card ↥(A ⊓ Subgroup.normalizer (T : Set G)) := by
  rw [← Subgroup.subgroupOf_normalizer_eq h, ← inf_comm,
    ← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

lemma card_normalizer_map_conj (T : Subgroup G) (g : G) :
    Nat.card (Subgroup.normalizer ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      Nat.card (Subgroup.normalizer (T : Set G)) := by
  rw [← Subgroup.map_equiv_normalizer_eq T (MulAut.conj g)]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

lemma card_sup_of_commute {S₁ S₂ : Subgroup G} (hcomm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x)
    (hinf : S₁ ⊓ S₂ = ⊥) : Nat.card ↥(S₁ ⊔ S₂) = Nat.card S₁ * Nat.card S₂ := by
  let φ : S₁ × S₂ →* G :=
    MonoidHom.noncommCoprod S₁.subtype S₂.subtype fun x y => hcomm x x.2 y y.2
  have hφ : ∀ x : S₁, ∀ y : S₂, φ (x, y) = (x : G) * y := fun x y => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ h
    rw [hφ] at h
    have hx : (x : G) = ((y : G))⁻¹ := eq_inv_of_mul_eq_one_left h
    have hxy : (x : G) ∈ S₁ ⊓ S₂ := ⟨x.2, hx ▸ S₂.inv_mem y.2⟩
    rw [hinf, Subgroup.mem_bot] at hxy
    have hy : (y : G) = 1 := by rw [hxy, one_mul] at h; exact h
    exact Prod.ext (Subtype.ext hxy) (Subtype.ext hy)
  have hrange : φ.range = S₁ ⊔ S₂ := by
    apply le_antisymm
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      rw [hφ]
      exact mul_mem (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right y.2)
    · refine sup_le (fun x hx => ⟨(⟨x, hx⟩, 1), ?_⟩) (fun y hy => ⟨(1, ⟨y, hy⟩), ?_⟩)
      · rw [hφ]; simp
      · rw [hφ]; simp
  rw [← hrange, ← Nat.card_prod, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

lemma two_mul_card_dvd [Finite G] {H N : Subgroup G} (hHN : H ≤ N) {t : G} (htN : t ∈ N)
    (htH : t ∈ Subgroup.normalizer (H : Set G)) (ht2 : t * t ∈ H) (ht : t ∉ H) :
    2 * Nat.card H ∣ Nat.card N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₁ : Subgroup G := N ⊓ Subgroup.normalizer (H : Set G) with hN₁
  have hH₁ : H ≤ N₁ := le_inf hHN Subgroup.le_normalizer
  have hnorm : (H.subgroupOf N₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH₁).2 inf_le_right
  let t₁ : N₁ := ⟨t, htN, htH⟩
  have h2 : (QuotientGroup.mk t₁ : N₁ ⧸ H.subgroupOf N₁) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, pow_two]
    exact ht2
  have h1 : (QuotientGroup.mk t₁ : N₁ ⧸ H.subgroupOf N₁) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ht
  have hord := orderOf_eq_prime h2 h1
  have hdvd : 2 ∣ (H.subgroupOf N₁).index := by
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hcard : Nat.card (H.subgroupOf N₁) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₁).toEquiv
  have hmul := Subgroup.card_mul_index (H.subgroupOf N₁)
  rw [hcard] at hmul
  have hN₁N : Nat.card N₁ ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
  refine dvd_trans ?_ hN₁N
  rw [← hmul, mul_comm (Nat.card H)]
  exact Nat.mul_dvd_mul hdvd dvd_rfl

end Generic

section Suzuki

variable {G : Type*} [Group G]

lemma map_conj_conj_of_mul_self {t : G} (ht2 : t * t = 1) (S : Subgroup G) :
    (S.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = S := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    convert hy using 1
    simp only [hti, mul_assoc]
    rw [← mul_assoc, ht2, one_mul, mul_one]
  · intro hx
    refine ⟨t * x * t⁻¹, ⟨x, hx, rfl⟩, ?_⟩
    simp only [hti, mul_assoc]
    rw [← mul_assoc, ht2, one_mul, mul_one]

lemma mem_normalizer_of_commute {S : Subgroup G} {x : G} (h : ∀ y ∈ S, x * y = y * x) :
    x ∈ Subgroup.normalizer (S : Set G) :=
  Subgroup.centralizer_le_normalizer (S : Set G)
    (Subgroup.mem_centralizer_iff.2 fun y hy => (h y hy).symm)

lemma map_conj_eq_of_commute {S : Subgroup G} {x : G} (h : ∀ y ∈ S, x * y = y * x) :
    S.map (MulAut.conj x).toMonoidHom = S :=
  map_conj_eq_of_mem_normalizer (mem_normalizer_of_commute h)

lemma card_sup_conj_of_swap {A B T : Subgroup G} {t : G} (hTA : T ≤ A)
    (hAB : A ⊓ B = ⊥) (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hBt : A.map (MulAut.conj t).toMonoidHom = B) :
    Nat.card ↥(T ⊔ T.map (MulAut.conj t).toMonoidHom) = Nat.card T * Nat.card T := by
  have hTB : T.map (MulAut.conj t).toMonoidHom ≤ B := hBt ▸ Subgroup.map_mono hTA
  rw [card_sup_of_commute (fun x hx y hy => hcomm x (hTA hx) y (hTB hy)) ?_,
    Subgroup.card_map_of_injective (MulAut.conj t).injective]
  rw [eq_bot_iff, ← hAB]
  exact inf_le_inf hTA hTB

theorem twenty_thousand_dvd_card_normalizer [Finite G] (Γ A B T : Subgroup G) (t : G) (hAΓ : A ≤ Γ)
    (htΓ : t ∈ Γ) (hTA : T ≤ A) (hT : Nat.card T = 25)
    (hNA : Nat.card ↥(A ⊓ Subgroup.normalizer (T : Set G)) = 100)
    (hAB : A ⊓ B = ⊥) (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hBt : A.map (MulAut.conj t).toMonoidHom = B) (ht2 : t * t = 1) :
    20000 ∣ Nat.card ↥(Γ ⊓
      Subgroup.normalizer ((T ⊔ T.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) := by
  set TB : Subgroup G := T.map (MulAut.conj t).toMonoidHom with hTBdef
  set P : Subgroup G := T ⊔ TB with hP
  set NA : Subgroup G := A ⊓ Subgroup.normalizer (T : Set G) with hNAdef
  set NB : Subgroup G := NA.map (MulAut.conj t).toMonoidHom with hNBdef
  have hTB : TB ≤ B := hBt ▸ Subgroup.map_mono hTA
  have hNAA : NA ≤ A := inf_le_left
  have hNBB : NB ≤ B := hBt ▸ Subgroup.map_mono hNAA
  have hNAcomm : ∀ x ∈ NA, ∀ y ∈ TB, x * y = y * x := fun x hx y hy =>
    hcomm x (hNAA hx) y (hTB hy)
  have hNAP : NA ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : T.map (MulAut.conj x).toMonoidHom = T :=
      map_conj_eq_of_mem_normalizer hx.2
    have h2 : TB.map (MulAut.conj x).toMonoidHom = TB :=
      map_conj_eq_of_commute (hNAcomm x hx)
    show P.map (MulAut.conj x).toMonoidHom = P
    rw [hP, Subgroup.map_sup, h1, h2]
  have htP : t ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show P.map (MulAut.conj t).toMonoidHom = P
    rw [hP, Subgroup.map_sup, map_conj_conj_of_mul_self ht2, sup_comm]
  have hNBP : NB ≤ Subgroup.normalizer (P : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem htP (hNAP hx)) (inv_mem htP)
  set H : Subgroup G := NA ⊔ NB with hH
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := sup_le hNAP hNBP
  have hNAΓ : NA ≤ Γ := hNAA.trans hAΓ
  have hNBΓ : NB ≤ Γ := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem htΓ (hNAΓ hx)) (inv_mem htΓ)
  have hHΓ : H ≤ Γ ⊓ Subgroup.normalizer (P : Set G) := le_inf (sup_le hNAΓ hNBΓ) hHP
  have hNBc : Nat.card NB = 100 := by
    rw [hNBdef, Subgroup.card_map_of_injective (MulAut.conj t).injective]; exact hNA
  have hHc : Nat.card H = 100 * 100 := by
    rw [hH, card_sup_of_commute (fun x hx y hy => hcomm x (hNAA hx) y (hNBB hy)), hNA, hNBc]
    rw [eq_bot_iff, ← hAB]
    exact inf_le_inf hNAA hNBB
  have htH : t ∈ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show H.map (MulAut.conj t).toMonoidHom = H
    rw [hH, Subgroup.map_sup, ← hNBdef, hNBdef, map_conj_conj_of_mul_self ht2, sup_comm]
  have htnH : t ∉ H := by
    intro htH'
    have hHA : H ≤ Subgroup.normalizer (A : Set G) := by
      refine sup_le (hNAA.trans Subgroup.le_normalizer) (fun y hy => ?_)
      exact mem_normalizer_of_commute fun a ha => (hcomm a ha y (hNBB hy)).symm
    have := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hHA htH')
    have hAB' : A = B := by rw [← hBt]; exact this.symm
    have hA1 : A = ⊥ := by rw [← inf_idem A]; nth_rewrite 2 [hAB']; exact hAB
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ T, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Nat.card T ≤ 1 := by
        have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
        rw [Finite.card_le_one_iff_subsingleton]
        exact ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
      omega
    exact hx1 (by simpa [hA1] using hTA hx)
  have hdvd := two_mul_card_dvd hHΓ (t := t) ⟨htΓ, htP⟩ htH (by rw [ht2]; exact one_mem _) htnH
  rw [hHc] at hdvd
  simpa using hdvd

end Suzuki

section Plane

open CFSG.Open CFSG.RankThree.PartOne.K1214 CFSG.HardMathSupport.Malle.Proving

variable {Γ : Type} [Group Γ] [Finite Γ]

lemma exists_plane_of_sylowShape (hsh : SylowShape 5 2 2 Γ) (P : Sylow 5 Γ) :
    ∃ E : Subgroup Γ, E ≤ (P : Subgroup Γ) ∧ IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := hsh (P : Subgroup Γ) P.isPGroup' P.not_dvd_index
  have e' : (P : Subgroup Γ) ≃* Hc := e
  let E₀ : Subgroup Hc := (powMonoidHom 5 : Hc →* Hc).ker
  let E : Subgroup Γ := (E₀.map e'.symm.toMonoidHom).map (P : Subgroup Γ).subtype
  have hmem : ∀ x : Γ, x ∈ E ↔ ∃ v ∈ E₀, ((e'.symm v : (P : Subgroup Γ)) : Γ) = x := by
    intro x
    simp only [E, Subgroup.mem_map, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  have hv5 : ∀ v ∈ E₀, v ^ 5 = 1 := fun v hv => by
    simpa [E₀, MonoidHom.mem_ker, powMonoidHom_apply] using hv
  refine ⟨E, ?_, (isElemAbelian_iff E).2 ⟨?_, ?_⟩, ?_⟩
  · rintro x hx
    obtain ⟨v, -, rfl⟩ := (hmem x).1 hx
    exact (e'.symm v).2
  · intro a ha b hb
    obtain ⟨v, -, rfl⟩ := (hmem a).1 ha
    obtain ⟨w, -, rfl⟩ := (hmem b).1 hb
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm v w]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := (hmem x).1 hx
    rw [← Subgroup.coe_pow, ← map_pow, hv5 v hv, map_one]
    rfl
  · rw [Subgroup.card_map_of_injective (Subtype.val_injective),
      Subgroup.card_map_of_injective e'.symm.injective]
    exact card_pow_five_ker

lemma normalizer_plane_eq (hsh : SylowShape 5 2 2 Γ)
    (hC : ∀ (P : Sylow 5 Γ) (E : Subgroup Γ), E ≤ (P : Subgroup Γ) → IsElemAbelian 5 E →
      Nat.card E = 5 ^ 2 → Subgroup.centralizer (E : Set Γ) = (P : Subgroup Γ))
    (P : Sylow 5 Γ) {E : Subgroup Γ} (hEP : E ≤ (P : Subgroup Γ)) (hE : IsElemAbelian 5 E)
    (hEc : Nat.card E = 5 ^ 2) :
    Subgroup.normalizer (E : Set Γ) = Subgroup.normalizer ((P : Subgroup Γ) : Set Γ) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply le_antisymm (normalizer_le_normalizer_of_centralizer_eq (hC P E hEP hE hEc))
  intro g hg
  obtain ⟨e⟩ := hsh (P : Subgroup Γ) P.isPGroup' P.not_dvd_index
  have e' : (P : Subgroup Γ) ≃* Hc := e
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup Γ) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg x).1 (hEP hx) |> fun h => by
      simpa [MulAut.conj_apply] using h
  have h5 : ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, x ^ 5 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  exact eq_of_exponent_five_of_homocyclic e' hle hEP h5 hE.2
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]; norm_num)
    (by rw [hEc]; norm_num)

theorem relIndex_normalizer_dvd (hsh : SylowShape 5 2 2 Γ)
    (hC : ∀ (P : Sylow 5 Γ) (E : Subgroup Γ), E ≤ (P : Subgroup Γ) → IsElemAbelian 5 E →
      Nat.card E = 5 ^ 2 → Subgroup.centralizer (E : Set Γ) = (P : Subgroup Γ))
    (P : Sylow 5 Γ) :
    (P : Subgroup Γ).relIndex (Subgroup.normalizer ((P : Subgroup Γ) : Set Γ)) ∣ 96 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨E, hEP, hE, hEc⟩ := exists_plane_of_sylowShape hsh P
  rw [← normalizer_plane_eq hsh hC P hEP hE hEc]
  have hCE := hC P E hEP hE hEc
  obtain ⟨φ, hφ⟩ := exists_coord_of_isElemAbelian hE hEc
  set N := Subgroup.normalizer (E : Set Γ) with hNdef
  set T : Subgroup Γ := (P : Subgroup Γ) with hTdef
  have hTC : T ≤ Subgroup.centralizer (E : Set Γ) := hCE.ge
  have hTN : T ≤ N := hCE.ge.trans (Subgroup.centralizer_le_normalizer _)
  let ρ : N →* (Vec5 ≃ₗ[ZMod 5] Vec5) := (linHom φ hφ).comp E.normalizerMonoidHom
  have hkerρ : ρ.ker = T.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show linHom φ hφ (E.normalizerMonoidHom x) = 1 ↔ _
    rw [linHom_eq_one_iff, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact hCE.le h
    · intro h
      exact hCE.ge h
  have hcardRange : Nat.card ↥ρ.range = T.relIndex N := by
    calc Nat.card ↥ρ.range = Nat.card (N ⧸ ρ.ker) :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).symm.toEquiv
      _ = (T.subgroupOf N).index := by rw [← hkerρ]; rfl
      _ = T.relIndex N := rfl
  have hdvdT : T.relIndex N ∣ T.index := ⟨N.index, (Subgroup.relIndex_mul_index hTN).symm⟩
  have hnd5 : ¬ 5 ∣ Nat.card ↥ρ.range := by
    rw [hcardRange]
    exact fun h => P.not_dvd_index (dvd_trans h hdvdT)
  have : Finite (Vec5 ≃ₗ[ZMod 5] Vec5) :=
    Finite.of_injective (fun e : Vec5 ≃ₗ[ZMod 5] Vec5 => (e : Vec5 → Vec5))
      LinearEquiv.coe_injective
  have h1 : Nat.card ↥ρ.range ∣ 96 * 5 := by
    have h480 := Subgroup.card_subgroup_dvd_card ρ.range
    rw [card_linEquiv] at h480
    rw [show (96 : ℕ) * 5 = 480 by norm_num]
    exact h480
  have hcop : Nat.Coprime (Nat.card ↥ρ.range) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hnd5).symm
  rw [← hcardRange]
  exact hcop.dvd_of_dvd_mul_right h1

open scoped Pointwise in
theorem six_dvd_relIndex_normalizer (hsh : SylowShape 5 2 2 Γ)
    (hC : ∀ (P : Sylow 5 Γ) (E : Subgroup Γ), E ≤ (P : Subgroup Γ) → IsElemAbelian 5 E →
      Nat.card E = 5 ^ 2 → Subgroup.centralizer (E : Set Γ) = (P : Subgroup Γ))
    (hplane : ∃ (R : Subgroup Γ) (i j h t : Γ), (∀ r ∈ R, r ^ 5 = 1) ∧ Nat.card R = 5 ^ 2 ∧
      CFSG.Quasithin.B45Tor.IsGL23Data R i j h t)
    (P : Sylow 5 Γ) :
    6 ∣ (P : Subgroup Γ).relIndex (Subgroup.normalizer ((P : Subgroup Γ) : Set Γ)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨E, hEP, hE, hEc⟩ := exists_plane_of_sylowShape hsh P
  rw [← normalizer_plane_eq hsh hC P hEP hE hEc]
  have hCE := hC P E hEP hE hEc
  obtain ⟨R, i, j, h, t, hR5, hRc, hd⟩ := hplane
  have hshT : SylowShape 5 2 2 (⊤ : Subgroup Γ) := SylowShape.of_mulEquiv Subgroup.topEquiv hsh
  obtain ⟨g, hg⟩ := exists_conj_eq_plane (⊤ : Subgroup Γ) hshT P E (le_inf hEP le_top) hE.2 hEc
    R le_top hR5 hRc
  have hGL : CFSG.Quasithin.B45Tor.IsGL23Data E ((MulAut.conj g).toMonoidHom i)
      ((MulAut.conj g).toMonoidHom j) ((MulAut.conj g).toMonoidHom h)
      ((MulAut.conj g).toMonoidHom t) := by
    rw [hg]; exact isGL23Data_map _ hd
  have hQ := hGL.toIsQ8Data
  set N := Subgroup.normalizer (E : Set Γ) with hNdef
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 5 (by rw [hEc]; norm_num)
  set F : Subgroup Γ := Subgroup.zpowers (x : Γ) with hF
  have hFE : F ≤ E := (Subgroup.zpowers_le).2 x.2
  have hFc : Nat.card F = 5 := by
    rw [hF, Nat.card_zpowers, orderOf_submonoid, hx]
  let φN : N →* MulAut Γ := (MulAut.conj : Γ →* MulAut Γ).comp N.subtype
  let _ : MulAction N (Subgroup Γ) := MulAction.compHom (Subgroup Γ) φN
  have hsmul : ∀ (n : N) (M : Subgroup Γ), n • M = M.map (MulAut.conj (n : Γ)).toMonoidHom :=
    fun n M => rfl
  have horbit : MulAction.orbit N F = {M : Subgroup Γ | M ≤ E ∧ Nat.card M = 5} := by
    ext M
    constructor
    · rintro ⟨n, rfl⟩
      show n • F ∈ _
      rw [hsmul]
      refine ⟨?_, ?_⟩
      · rintro _ ⟨y, hy, rfl⟩
        have := (Subgroup.mem_normalizer_iff.1 n.2 y).1 (hFE hy)
        simpa [MulAut.conj_apply] using this
      · rw [Subgroup.card_map_of_injective (MulAut.conj (n : Γ)).injective, hFc]
    · rintro ⟨hME, hMc⟩
      obtain ⟨n, hn, hnF⟩ := lines_transitive_of_isQ8Data hE hEc hQ F M hFE hME hFc hMc
      exact ⟨⟨n, hn⟩, by show (⟨n, hn⟩ : N) • F = M; rw [hsmul]; exact hnF⟩
  have hidx : (MulAction.stabilizer N F).index = 6 := by
    rw [MulAction.index_stabilizer, horbit,
      CFSG.Quasithin.B45Tor.ncard_lines_of_plane hEc hE.2]
  have hle : (P : Subgroup Γ).subgroupOf N ≤ MulAction.stabilizer N F := by
    intro n hn
    rw [Subgroup.mem_subgroupOf, ← hCE] at hn
    rw [MulAction.mem_stabilizer_iff, hsmul]
    exact map_conj_eq_of_commute fun y hy =>
      (Subgroup.mem_centralizer_iff.1 hn y (hFE hy)).symm
  rw [← hidx]
  exact Subgroup.index_dvd_of_le hle

lemma pow_factorization_eq (hsh : SylowShape 5 2 2 Γ) :
    5 ^ (Nat.card Γ).factorization 5 = 5 ^ 4 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 5 Γ) := inferInstance
  obtain ⟨e⟩ := hsh (Q : Subgroup Γ) Q.isPGroup' Q.not_dvd_index
  have e' : (Q : Subgroup Γ) ≃* Hc := e
  rw [← Sylow.card_eq_multiplicity Q, Nat.card_congr e'.toEquiv, card_Hc]

end Plane

section ReeGamma

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution
open CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ12
open CFSG.AGLEmbedding.KFactProofs.Sz32Local CFSG.AGLEmbedding.KFactProofs.Sz32

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem card_normalizer_sylow_rankOneGroupTwo
    (hK : Nat.card K = 2 ^ (2 * 2 + 1))
    (T : Sylow 5 ↥(rankOneGroupTwo K 2)) :
    Nat.card (Subgroup.normalizer ((T : Subgroup ↥(rankOneGroupTwo K 2)) : Set ↥(rankOneGroupTwo K 2))) = 100 ∧
      Nat.card (T : Subgroup ↥(rankOneGroupTwo K 2)) = 25 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have e := rankOneEquivSuzuki K 2 (by norm_num) hK
  have hiso := isoLie_suzuki_of_blueprint (A := ↥(rankOneGroupTwo K 2)) (m := 2) (by norm_num) hK e
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  let σ : K ≃+* F32 := F32.ringEquiv K hK
  let ε : ↥(rankOneGroupTwo K 2) ≃* suzukiGroup 2 F32 := e.trans (modelEquiv σ)
  have hcard : Nat.card (T : Subgroup ↥(rankOneGroupTwo K 2)) = 25 := by
    rw [Sylow.card_eq_multiplicity, hSz.card, CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
    norm_num
  have hdata : CFSG.AGLEmbedding.KFactProofs.Sz32Local.Sz32Data ↥(rankOneGroupTwo K 2)
      (T : Subgroup ↥(rankOneGroupTwo K 2)) :=
    ⟨hSz.card, hcard, hSz.cyclic T, centralizer_le_of_equiv ε T⟩
  exact ⟨hdata.card_normalizer, hcard⟩

theorem exists_sylow_twenty_thousand_dvd
    (hK : Nat.card K = 2 ^ (2 * 2 + 1))
    (hsh : CFSG.RankThree.PartOne.K1214.SylowShape 5 2 2 (F4.reeGamma K 2)) :
    ∃ P : Sylow 5 ↥(F4.reeGamma K 2),
      20000 ∣ Nat.card (Subgroup.normalizer
        ((P : Subgroup ↥(F4.reeGamma K 2)) : Set ↥(F4.reeGamma K 2))) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have : Finite ↥(F4.reeGamma K 2) := Subtype.finite
  set R : Subgroup (ModGL F4.tag K) := rankOneGroupTwo K 2 with hR
  set t : ModGL F4.tag K := szNw K with ht
  have hRΓ : R ≤ F4.reeGamma K 2 := rankOneGroupTwo_le_reeGamma' hK
  have htΓ : t ∈ F4.reeGamma K 2 := szNw_mem_reeGamma
  have hBΓ : szSubB K 2 ≤ F4.reeGamma K 2 := szSubB_le_reeGamma hK
  have hcomm : ∀ x ∈ R, ∀ y ∈ szSubB K 2, x * y = y * x := commute_rankOneGroupTwo_szSubB
  have hAB : R ⊓ szSubB K 2 = ⊥ := rankOneGroupTwo_inf_szSubB (by norm_num) hK
  have ht2 : t * t = 1 := szNw_mul_self
  have hBt : R.map (MulAut.conj t).toMonoidHom = szSubB K 2 := rfl
  obtain ⟨T₀⟩ : Nonempty (Sylow 5 ↥R) := inferInstance
  obtain ⟨hN, hTc⟩ := card_normalizer_sylow_rankOneGroupTwo hK T₀
  set T : Subgroup (ModGL F4.tag K) := (T₀ : Subgroup ↥R).map R.subtype with hT
  have hTR : T ≤ R := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hTsub : T.subgroupOf R = (T₀ : Subgroup ↥R) := by
    exact Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
  have hT25 : Nat.card T = 25 := by
    rw [hT, Subgroup.card_map_of_injective R.subtype_injective, hTc]
  have hNA : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set (ModGL F4.tag K))) = 100 := by
    rw [← card_normalizer_subgroupOf R T hTR, hTsub]
    exact hN
  have h20000 := twenty_thousand_dvd_card_normalizer (F4.reeGamma K 2) R (szSubB K 2) T t hRΓ htΓ
    hTR hT25 hNA hAB hcomm hBt ht2
  set P'' : Subgroup (ModGL F4.tag K) := T ⊔ T.map (MulAut.conj t).toMonoidHom with hP''
  have hP''Γ : P'' ≤ F4.reeGamma K 2 := by
    refine sup_le (hTR.trans hRΓ) ?_
    rw [← hBt] at hBΓ
    exact (Subgroup.map_mono hTR).trans hBΓ
  have hP''c : Nat.card P'' = 5 ^ 4 := by
    rw [hP'', card_sup_conj_of_swap hTR hAB hcomm hBt, hT25]
    norm_num
  have hcardP : Nat.card (P''.subgroupOf (F4.reeGamma K 2)) =
      5 ^ (Nat.card ↥(F4.reeGamma K 2)).factorization 5 := by
    rw [pow_factorization_eq hsh, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP''Γ).toEquiv,
      hP''c]
  refine ⟨Sylow.ofCard _ hcardP, ?_⟩
  rw [Sylow.coe_ofCard, card_normalizer_subgroupOf _ _ hP''Γ]
  exact h20000

theorem sylowShape_reeGamma (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    CFSG.RankThree.PartOne.K1214.SylowShape 5 2 2 (F4.reeGamma K 2) := by
  have := CFSG.RankThree.PartOne.K128.sylowShape_ree_phi4 (K := K) (a := 2) hK Nat.prime_five
    (by norm_num) (by norm_num)
  rwa [factorization_five_phi4] at this

theorem relIndex_sylow_normalizer
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) (P : Sylow 5 ↥(F4.reeGamma K 2)) :
    (P : Subgroup ↥(F4.reeGamma K 2)).relIndex (Subgroup.normalizer
      ((P : Subgroup ↥(F4.reeGamma K 2)) : Set ↥(F4.reeGamma K 2))) = 96 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have : Finite ↥(F4.reeGamma K 2) := Subtype.finite
  have hsh := sylowShape_reeGamma hK
  have hC : ∀ (P : Sylow 5 ↥(F4.reeGamma K 2)) (E : Subgroup ↥(F4.reeGamma K 2)),
      E ≤ (P : Subgroup _) → CFSG.Open.IsElemAbelian 5 E → Nat.card E = 5 ^ 2 →
      Subgroup.centralizer (E : Set ↥(F4.reeGamma K 2)) = (P : Subgroup _) :=
    fun P E hEP hE hEc => centralizer_plane_eq_sylow hK P E hEP hE hEc
  have hplane : ∃ (R : Subgroup ↥(F4.reeGamma K 2)) (i j h t : ↥(F4.reeGamma K 2)),
      (∀ r ∈ R, r ^ 5 = 1) ∧ Nat.card R = 5 ^ 2 ∧
        CFSG.Quasithin.B45Tor.IsGL23Data R i j h t := by
    obtain ⟨R, i, j, h, t, -, hR5, hRc, hGL, -, -⟩ :=
      CFSG.Quasithin.B45Tor.exists_reePlane (K := K) (a := 2) (by norm_num) hK
        (p := 5) Nat.prime_five (by norm_num) (Or.inl (by norm_num))
    exact ⟨R, i, j, h, t, hR5, hRc, hGL⟩
  have h96 := relIndex_normalizer_dvd hsh hC P
  have h6 := six_dvd_relIndex_normalizer hsh hC hplane P
  obtain ⟨P₀, h20000⟩ := exists_sylow_twenty_thousand_dvd hK hsh
  have hconj : Nat.card (Subgroup.normalizer
        ((P : Subgroup ↥(F4.reeGamma K 2)) : Set ↥(F4.reeGamma K 2))) =
      Nat.card (Subgroup.normalizer
        ((P₀ : Subgroup ↥(F4.reeGamma K 2)) : Set ↥(F4.reeGamma K 2))) := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(F4.reeGamma K 2) P₀ P
    have := coe_smul_sylow_eq_map P₀ g
    rw [hg] at this
    rw [this, card_normalizer_map_conj]
  have hPc : Nat.card (P : Subgroup ↥(F4.reeGamma K 2)) = 5 ^ 4 := by
    rw [Sylow.card_eq_multiplicity, pow_factorization_eq hsh]
  have hmul := Subgroup.relIndex_mul_card (H := (P : Subgroup ↥(F4.reeGamma K 2)))
    (K := Subgroup.normalizer ((P : Subgroup ↥(F4.reeGamma K 2)) : Set ↥(F4.reeGamma K 2)))
  rw [inf_eq_left.2 Subgroup.le_normalizer, hPc] at hmul
  set r := (P : Subgroup ↥(F4.reeGamma K 2)).relIndex (Subgroup.normalizer
    ((P : Subgroup ↥(F4.reeGamma K 2)) : Set ↥(F4.reeGamma K 2))) with hr
  rw [← hconj, ← hmul] at h20000
  have h32 : 32 ∣ r := by
    have : 5 ^ 4 * 32 ∣ 5 ^ 4 * r := by
      rw [show 5 ^ 4 * 32 = 20000 by norm_num, mul_comm]
      exact h20000
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 this
  have h3 : 3 ∣ r := (Dvd.intro 2 rfl : 3 ∣ 6).trans h6
  have h96' : 96 ∣ r := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 32 3) h32 h3
    simpa using this
  exact Nat.dvd_antisymm h96 h96'

theorem card_normalizer_sylow_reeGamma
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) (P : Sylow 5 ↥(F4.reeGamma K 2)) :
    Nat.card (Subgroup.normalizer
      ((P : Subgroup ↥(F4.reeGamma K 2)) : Set ↥(F4.reeGamma K 2))) = 60000 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have : Finite ↥(F4.reeGamma K 2) := Subtype.finite
  have hsh := sylowShape_reeGamma hK
  have hPc : Nat.card (P : Subgroup ↥(F4.reeGamma K 2)) = 5 ^ 4 := by
    rw [Sylow.card_eq_multiplicity, pow_factorization_eq hsh]
  have hmul := Subgroup.relIndex_mul_card (H := (P : Subgroup ↥(F4.reeGamma K 2)))
    (K := Subgroup.normalizer ((P : Subgroup ↥(F4.reeGamma K 2)) : Set ↥(F4.reeGamma K 2)))
  rw [inf_eq_left.2 Subgroup.le_normalizer, hPc, relIndex_sylow_normalizer hK P] at hmul
  rw [← hmul]
  norm_num

end ReeGamma

end CFSG.HardMathSupport.Malle.LocalAction
