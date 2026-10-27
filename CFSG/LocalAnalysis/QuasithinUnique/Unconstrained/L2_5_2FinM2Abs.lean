module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinGen
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents

public section

namespace CFSG.QuasithinUnique.Unc25G2

open CFSG.Open CFSG.Quasithin

namespace M2x

section Span

variable {X : Type*} [Group X]

@[expose] def spanList : List X → List X
  | [] => [1]
  | e :: l => spanList l ++ (spanList l).map (e * ·)

theorem mem_spanList_cons {e : X} {l : List X} {x : X} :
    x ∈ spanList (e :: l) ↔ x ∈ spanList l ∨ ∃ y ∈ spanList l, x = e * y := by
  simp [spanList, eq_comm]

theorem exists_span [Finite X] (k : ℕ) :
    ∀ E : Subgroup X, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E = 2 ^ k →
      ∃ l : List X, l.length = k ∧ (∀ e ∈ l, e ∈ E) ∧ ∀ x ∈ E, x ∈ spanList l := by
  induction k with
  | zero =>
    intro E _ _ hc
    refine ⟨[], rfl, by simp, fun x hx => ?_⟩
    have hE : E = ⊥ := Subgroup.card_eq_one.mp (by simpa using hc)
    rw [hE, Subgroup.mem_bot] at hx
    simp [spanList, hx]
  | succ k ih =>
    intro E hcomm hsq hcard
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2k : 2 ^ k ∣ Nat.card E := by rw [hcard]; exact pow_dvd_pow 2 (Nat.le_succ k)
    obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 2 h2k
    set F : Subgroup X := F₀.map E.subtype with hFdef
    have hFE : F ≤ E := fun x hx => by
      obtain ⟨y, _, rfl⟩ := hx
      exact y.2
    have hFcard : Nat.card F = 2 ^ k := by
      rw [hFdef, Subgroup.card_map_of_injective E.subtype_injective, hF₀]
    obtain ⟨l, hl, hlF, hspan⟩ := ih F (fun x hx y hy => hcomm x (hFE hx) y (hFE hy))
      (fun x hx => hsq x (hFE hx)) hFcard
    obtain ⟨e, heE, heF⟩ : ∃ e ∈ E, e ∉ F := by
      by_contra h
      push Not at h
      have hle : E ≤ F := h
      have := Subgroup.card_le_of_le hle
      rw [hcard, hFcard] at this
      have : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
      omega
    have hidx : (F.subgroupOf E).index = 2 := by
      have h := (F.subgroupOf E).card_mul_index
      have hc : Nat.card (F.subgroupOf E) = 2 ^ k := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv, hFcard]
      rw [hc, hcard] at h
      have : 2 ^ k * (F.subgroupOf E).index = 2 ^ k * 2 := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
    have hmul : ∀ x ∈ E, x ∉ F → x * e ∈ F := by
      intro x hx hxF
      have hnot : ∀ z : ↥E, (z : X) ∉ F → z * a ∈ F.subgroupOf E := by
        intro z hz
        rcases ha z with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd (Subgroup.mem_subgroupOf.mp h1) hz
      have h1 := hnot ⟨x, hx⟩ hxF
      have h2 := hnot ⟨e, heE⟩ heF
      have h3 := (F.subgroupOf E).mul_mem h1 ((F.subgroupOf E).inv_mem h2)
      rw [Subgroup.mem_subgroupOf] at h3
      have h4 : ((⟨x, hx⟩ * a * (⟨e, heE⟩ * a)⁻¹ : ↥E) : X) = x * e⁻¹ := by
        simp [mul_assoc]
      rw [h4] at h3
      have hee : e⁻¹ = e := by
        have := hsq e heE
        exact inv_eq_of_mul_eq_one_right this
      rwa [hee] at h3
    refine ⟨e :: l, by simp [hl], ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact heE
      · exact hFE (hlF x hx)
    · intro x hx
      rw [mem_spanList_cons]
      by_cases hxF : x ∈ F
      · exact Or.inl (hspan x hxF)
      · refine Or.inr ⟨x * e, hspan _ (hmul x hx hxF), ?_⟩
        have h1 := hsq e heE
        have h2 := hcomm x hx e heE
        have h3 : e * (x * e) = x := by
          rw [← mul_assoc, ← h2, mul_assoc, h1, mul_one]
        exact h3.symm

end Span

section SylowTwo

theorem isPGroup_subgroupOf {G : Type*} [Group G] {P : Subgroup G} (L : Subgroup G)
    (hP : IsPGroup 2 P) : IsPGroup 2 (P.subgroupOf L) := by
  intro g
  obtain ⟨k, hk⟩ := hP ⟨((g.1 : ↥L) : G), Subgroup.mem_subgroupOf.mp g.2⟩
  have hk' : ((g.1 : ↥L) : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact ⟨k, Subtype.ext (Subtype.ext hk')⟩

theorem le_of_normal_pGroup_of_sylow {X : Type*} [Group X] [Finite X] {P Q E : Subgroup X}
    (hP2 : IsPGroup 2 P) (hodd : ¬ 2 ∣ (P.subgroupOf Q).index) (hEQ : E ≤ Q)
    (hEn : (E.subgroupOf Q).Normal) (hE2 : IsPGroup 2 E) : E ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPQ2 : IsPGroup 2 (P.subgroupOf Q) := isPGroup_subgroupOf Q hP2
  let S : Sylow 2 Q := hPQ2.toSylow hodd
  have hE2' : IsPGroup 2 (E.subgroupOf Q) := isPGroup_subgroupOf Q hE2
  have h := hE2'.le_sylow_of_normal S
  intro x hx
  have : (⟨x, hEQ hx⟩ : Q) ∈ E.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (h this)

end SylowTwo

section Defs

variable {Γ : Type*} [Group Γ]

@[expose] def ElemAb (E : Subgroup Γ) : Prop :=
  (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1

@[expose] def TwoEAt (P : Subgroup Γ) : Prop :=
  ∃ (Ea Eb : Subgroup Γ) (ga gb : Γ), Ea ≤ P ∧ Eb ≤ P ∧ Ea ≠ Eb ∧ ElemAb Ea ∧ ElemAb Eb ∧
    Nat.card Ea = 16 ∧ Nat.card Eb = 16 ∧
    (∀ E : Subgroup Γ, E ≤ P → ElemAb E → Nat.card E = 16 → E = Ea ∨ E = Eb) ∧
    (∀ x : Γ, (∀ e ∈ Ea, x * e = e * x) → x ∈ Ea) ∧
    (∀ x : Γ, (∀ e ∈ Eb, x * e = e * x) → x ∈ Eb) ∧
    (ga ∈ Subgroup.normalizer (Eb : Set Γ) ∧ ga ∉ Subgroup.normalizer (Ea : Set Γ)) ∧
    (gb ∈ Subgroup.normalizer (Ea : Set Γ) ∧ gb ∉ Subgroup.normalizer (Eb : Set Γ))

end Defs

@[expose] def TwoE (Γ : Type*) [Group Γ] : Prop :=
  ∃ P : Subgroup Γ, IsPGroup 2 P ∧ ¬ 2 ∣ P.index ∧ TwoEAt P

section Transport

variable {Γ Λ : Type*} [Group Γ] [Group Λ]

theorem ElemAb.map (e : Γ ≃* Λ) {E : Subgroup Γ} (h : ElemAb E) :
    ElemAb (E.map e.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show e x * e y = e y * e x
    rw [← map_mul, ← map_mul, h.1 x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    show e x * e x = 1
    rw [← map_mul, h.2 x hx, map_one]

theorem map_map_symm (e : Γ ≃* Λ) (E : Subgroup Γ) :
    (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Γ := by
    ext x; simp
  rw [this, Subgroup.map_id]

theorem map_symm_map (e : Γ ≃* Λ) (E : Subgroup Λ) :
    (E.map e.symm.toMonoidHom).map e.toMonoidHom = E := by
  rw [Subgroup.map_map]
  have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Λ := by
    ext x; simp
  rw [this, Subgroup.map_id]

theorem mem_normalizer_map_iff (e : Γ ≃* Λ) (E : Subgroup Γ) (g : Γ) :
    e g ∈ Subgroup.normalizer ((E.map e.toMonoidHom : Subgroup Λ) : Set Λ) ↔
      g ∈ Subgroup.normalizer (E : Set Γ) := by
  rw [← Subgroup.map_equiv_normalizer_eq E e, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem TwoEAt.map (e : Γ ≃* Λ) {P : Subgroup Γ} (h : TwoEAt P) : TwoEAt (P.map e.toMonoidHom) := by
  obtain ⟨Ea, Eb, ga, gb, hEaP, hEbP, hne, hEa, hEb, hca, hcb, hcl, hcena, hcenb,
    ⟨hga1, hga2⟩, ⟨hgb1, hgb2⟩⟩ := h
  have hcen : ∀ E : Subgroup Γ, (∀ x : Γ, (∀ f ∈ E, x * f = f * x) → x ∈ E) →
      ∀ x : Λ, (∀ f ∈ E.map e.toMonoidHom, x * f = f * x) → x ∈ E.map e.toMonoidHom := by
    intro E hE x hx
    have h1 : e.symm x ∈ E := by
      apply hE
      intro f hf
      have := hx (e f) ⟨f, hf, rfl⟩
      have h2 := congrArg e.symm this
      simpa only [map_mul, MulEquiv.symm_apply_apply] using h2
    exact ⟨e.symm x, h1, by simp⟩
  refine ⟨Ea.map e.toMonoidHom, Eb.map e.toMonoidHom, e ga, e gb, Subgroup.map_mono hEaP,
    Subgroup.map_mono hEbP, fun h => hne (Subgroup.map_injective e.injective h), hEa.map e,
    hEb.map e, (Subgroup.card_map_of_injective e.injective).trans hca,
    (Subgroup.card_map_of_injective e.injective).trans hcb, ?_, hcen Ea hcena, hcen Eb hcenb,
    ⟨(mem_normalizer_map_iff e Eb ga).mpr hga1, fun h => hga2 ((mem_normalizer_map_iff e Ea ga).mp h)⟩,
    ⟨(mem_normalizer_map_iff e Ea gb).mpr hgb1, fun h => hgb2 ((mem_normalizer_map_iff e Eb gb).mp h)⟩⟩
  intro E' hE'P hE'ab hE'c
  have hE₀P : E'.map e.symm.toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨p, hp, hpy⟩ := hE'P hy
    show e.symm y ∈ P
    rw [← hpy]
    simpa using hp
  have hE₀c : Nat.card (E'.map e.symm.toMonoidHom) = 16 :=
    (Subgroup.card_map_of_injective e.symm.injective).trans hE'c
  rcases hcl _ hE₀P (hE'ab.map e.symm) hE₀c with h | h
  · left
    rw [← map_symm_map e E', h]
  · right
    rw [← map_symm_map e E', h]

end Transport

theorem TwoE.of_equiv {Γ Λ : Type*} [Group Γ] [Group Λ] (h : TwoE Γ) (e : Γ ≃* Λ) : TwoE Λ := by
  obtain ⟨P, hP, hPi, hat⟩ := h
  refine ⟨P.map e.toMonoidHom, hP.map _, ?_, hat.map e⟩
  rwa [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective P]

theorem TwoE.exists_at {Γ : Type*} [Group Γ] [Finite Γ] (h : TwoE Γ) {P : Subgroup Γ}
    (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) : TwoEAt P := by
  obtain ⟨P₀, hP₀, hP₀i, hat⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_conj_map_eq hP₀ hP₀i hP hPi
  have := hat.map (MulAut.conj c)
  rwa [hc] at this

section Pair

variable {Λ : Type*} [Group Λ]

theorem pair_step {P E₁ E₂ : Subgroup Λ} (hne : E₁ ≠ E₂) (h₂P : E₂ ≤ P) (hE₂ : ElemAb E₂)
    (h₂c : Nat.card E₂ = 16)
    (hcl : ∀ E : Subgroup Λ, E ≤ P → ElemAb E → Nat.card E = 16 → E = E₁ ∨ E = E₂)
    (hcent : ∀ x : Λ, (∀ e ∈ E₂, x * e = e * x) → x ∈ E₂)
    {g : Λ} (hg₂ : g ∈ Subgroup.normalizer (E₂ : Set Λ))
    (hg₁ : g ∉ Subgroup.normalizer (E₁ : Set Λ))
    (Φ : MulAut Λ → Prop) (hΦP : ∀ α, Φ α → P.map α.toMonoidHom = P)
    (hΦE : ∀ α, Φ α → E₁.map α.toMonoidHom = E₁) :
    ∃ K V : Subgroup Λ, V ≤ K ∧ K ≤ Subgroup.normalizer (V : Set Λ) ∧ IsPGroup 2 V ∧
      (∀ x ∈ K, (∀ v ∈ V, x * v = v * x) → x ∈ V) ∧ (∀ α, Φ α → K.map α.toMonoidHom = K) ∧
      ¬ K ≤ Subgroup.normalizer (E₁ : Set Λ) := by
  have hE₂inv : ∀ α, Φ α → E₂.map α.toMonoidHom = E₂ := by
    intro α hα
    have hle : E₂.map α.toMonoidHom ≤ P := by
      rw [← hΦP α hα]; exact Subgroup.map_mono h₂P
    rcases hcl _ hle (hE₂.map α) ((Subgroup.card_map_of_injective α.injective).trans h₂c) with h | h
    · exfalso
      apply hne
      have : E₂.map α.toMonoidHom = E₁.map α.toMonoidHom := by rw [h, hΦE α hα]
      exact (Subgroup.map_injective α.injective this).symm
    · exact h
  refine ⟨Subgroup.normalizer (E₂ : Set Λ), E₂, Subgroup.le_normalizer, le_rfl, ?_,
    fun x _ hx => hcent x hx, ?_, fun hle => hg₁ (hle hg₂)⟩
  · exact IsPGroup.of_card (n := 4) (by rw [h₂c]; norm_num)
  · intro α hα
    rw [Subgroup.map_equiv_normalizer_eq E₂ α, hE₂inv α hα]

end Pair

theorem normal_two_le_ker {M A : Type*} [Group M] [Group A] [IsSimpleGroup A]
    (hA : ¬ IsPGroup 2 A) (α : M →* A) (hα : Function.Surjective α) (F : Subgroup M) [F.Normal]
    (hF : IsPGroup 2 F) : F ≤ α.ker := by
  have hN : (F.map α).Normal := Subgroup.Normal.map ‹F.Normal› α hα
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (F.map α) with h | h
  · intro x hx
    rw [MonoidHom.mem_ker]
    have : α x ∈ F.map α := ⟨x, hx, rfl⟩
    rw [h] at this
    simpa using this
  · exfalso
    apply hA
    have h2 : IsPGroup 2 (F.map α) := hF.map α
    rw [h] at h2
    exact h2.of_equiv Subgroup.topEquiv

theorem not_isPGroup_alternatingGroup (m : ℕ)
    (h : Nat.card (alternatingGroup (Fin m)) = 360 ∨ Nat.card (alternatingGroup (Fin m)) = 2520) :
    ¬ IsPGroup 2 (alternatingGroup (Fin m)) := by
  intro hp
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have h3 : 3 ∣ Nat.card (alternatingGroup (Fin m)) := by
    rcases h with h | h <;> rw [h] <;> norm_num
  rw [hn] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem m2x_excluded {G : Type} [Group G] [Finite G] {Γ : Type} [Group Γ] [Finite Γ]
    (hΓ : TwoE Γ) (L S₀ ML : Subgroup G) (ε : ↥L ≃* Γ) {m : ℕ}
    (hsimple : IsSimpleGroup (alternatingGroup (Fin m)))
    (hm : ¬ IsPGroup 2 (alternatingGroup (Fin m)))
    (hAlt : IsAltOverElemAbelian ML 4 m) (hMLL : ML ≤ L) (hS₀2 : IsPGroup 2 S₀)
    (hS₀N : S₀ ≤ Subgroup.normalizer (L : Set G)) (hsyl : IsSylowTwoOf (S₀ ⊓ L) L)
    (hS₀ML : S₀ ≤ Subgroup.normalizer (ML : Set G))
    (hall : ∀ K : Subgroup G, K ≤ L → S₀ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ ML) :
    False := by
  classical
  have := hsimple
  obtain ⟨E, α, hEML, hEab, hE16, hαs, hker⟩ := hAlt
  have hEL : E ≤ L := hEML.trans hMLL
  have hEnorm : ML ≤ Subgroup.normalizer (E : Set G) := by
    have hn : (E.subgroupOf ML).Normal := by rw [← hker]; infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hEML).mp hn
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := isMulCommutative_iff.mp hEab.1 ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := hEab.2 x hx
    simpa [pow_two] using this
  have hEfix : ∀ s ∈ S₀, ∀ x ∈ E, s * x * s⁻¹ ∈ E := by
    intro s hs x hx
    set F : Subgroup ↥ML := (E.map (MulAut.conj s).toMonoidHom).subgroupOf ML with hF
    have hsML : ∀ h : G, h ∈ ML ↔ s * h * s⁻¹ ∈ ML := Subgroup.mem_normalizer_iff.mp (hS₀ML hs)
    have hsML' : ∀ h : G, h ∈ ML ↔ s⁻¹ * h * s ∈ ML := by
      intro h
      have := Subgroup.mem_normalizer_iff.mp (hS₀ML (S₀.inv_mem hs)) h
      simpa using this
    have hFnormal : F.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨x', hx', hx'n⟩ := Subgroup.mem_subgroupOf.mp hn
      rw [Subgroup.mem_subgroupOf]
      refine ⟨(s⁻¹ * (g : G) * s) * x' * (s⁻¹ * (g : G) * s)⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hEnorm ((hsML' g).mp g.2)) x').mp hx'
      · have hn' : ((n : ↥ML) : G) = s * x' * s⁻¹ := hx'n.symm
        show s * ((s⁻¹ * (g : G) * s) * x' * (s⁻¹ * (g : G) * s)⁻¹) * s⁻¹ =
          (g : G) * ((n : ↥ML) : G) * (g : G)⁻¹
        rw [hn']
        group
    have hF2 : IsPGroup 2 F := by
      intro n
      refine ⟨1, ?_⟩
      obtain ⟨x', hx', hx'n⟩ := Subgroup.mem_subgroupOf.mp n.2
      have hn' : (((n : ↥F) : ↥ML) : G) = s * x' * s⁻¹ := hx'n.symm
      apply Subtype.ext
      apply Subtype.ext
      show (((n : ↥F) : ↥ML) : G) ^ 2 ^ 1 = 1
      rw [hn', pow_one, pow_two]
      calc s * x' * s⁻¹ * (s * x' * s⁻¹) = s * (x' * x') * s⁻¹ := by group
        _ = 1 := by rw [hEsq x' hx']; group
    have hle := normal_two_le_ker hm α hαs F hF2
    have hmem : (⟨s * x * s⁻¹, (hsML x).mp (hEML hx)⟩ : ↥ML) ∈ F :=
      Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩
    have := hle hmem
    rw [hker] at this
    exact Subgroup.mem_subgroupOf.mp this
  set EL : Subgroup ↥L := E.subgroupOf L with hELdef
  have hELab : ElemAb EL := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · exact Subtype.ext (hEcomm _ hx _ hy)
    · exact Subtype.ext (hEsq _ hx)
  have hEL16 : Nat.card EL = 16 := by
    have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
    rw [hELdef, this, hE16]
    norm_num
  have hEL2 : IsPGroup 2 EL := IsPGroup.of_card (n := 4) (by rw [hEL16]; norm_num)
  set P : Subgroup ↥L := (S₀ ⊓ L).subgroupOf L with hPdef
  have hP2 : IsPGroup 2 P := isPGroup_inf_subgroupOf L hS₀2
  have hPi : ¬ 2 ∣ P.index := hsyl.2.2
  have hPN : P ≤ Subgroup.normalizer (EL : Set ↥L) := by
    intro p hp
    have hpS : (p : G) ∈ S₀ := (Subgroup.mem_subgroupOf.mp hp).1
    rw [Subgroup.mem_normalizer_iff]
    intro h
    show (h : G) ∈ E ↔ ((p * h * p⁻¹ : ↥L) : G) ∈ E
    have e1 : ((p * h * p⁻¹ : ↥L) : G) = (p : G) * h * (p : G)⁻¹ := rfl
    rw [e1]
    constructor
    · exact hEfix _ hpS _
    · intro hh
      have := hEfix _ (S₀.inv_mem hpS) _ hh
      simpa [mul_assoc] using this
  have hELP : EL ≤ P := by
    set Q := Subgroup.normalizer (EL : Set ↥L) with hQ
    have hodd : ¬ 2 ∣ (P.subgroupOf Q).index := by
      intro h
      apply hPi
      have := Subgroup.relIndex_mul_index hPN
      exact h.trans ⟨Q.index, this.symm⟩
    exact le_of_normal_pGroup_of_sylow hP2 hodd Subgroup.le_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hEL2
  have hΓL : TwoE ↥L := hΓ.of_equiv ε.symm
  obtain ⟨Ea, Eb, ga, gb, hEaP, hEbP, hne, hEa, hEb, hca, hcb, hcl, hcena, hcenb,
    ⟨hga1, hga2⟩, ⟨hgb1, hgb2⟩⟩ := hΓL.exists_at hP2 hPi
  let Φ : MulAut ↥L → Prop := fun β => ∃ s, ∃ hs : s ∈ S₀, β = conjAut L s (hS₀N hs)
  have hΦP : ∀ β, Φ β → P.map β.toMonoidHom = P := by
    rintro β ⟨s, hs, rfl⟩
    exact map_conjAut_subgroupOf_eq hS₀N hs
  have hΦE : ∀ β, Φ β → EL.map β.toMonoidHom = EL := by
    rintro β ⟨s, hs, rfl⟩
    apply map_eq_of_forall_mem
    intro x hx
    show ((conjAut L s (hS₀N hs) x : ↥L) : G) ∈ E
    rw [coe_conjAut]
    exact hEfix s hs _ hx
  obtain ⟨K, V, hVK, hKn, hV2, hVc, hKinv, hKnot⟩ : ∃ K V : Subgroup ↥L, V ≤ K ∧
      K ≤ Subgroup.normalizer (V : Set ↥L) ∧ IsPGroup 2 V ∧
      (∀ x ∈ K, (∀ v ∈ V, x * v = v * x) → x ∈ V) ∧ (∀ β, Φ β → K.map β.toMonoidHom = K) ∧
      ¬ K ≤ Subgroup.normalizer (EL : Set ↥L) := by
    rcases hcl EL hELP hELab hEL16 with h | h
    · rw [h] at hΦE ⊢
      exact pair_step hne hEbP hEb hcb hcl hcenb hga1 hga2 Φ hΦP hΦE
    · rw [h] at hΦE ⊢
      exact pair_step hne.symm hEaP hEa hca (fun E hE hab hc => (hcl E hE hab hc).symm) hcena
        hgb1 hgb2 Φ hΦP hΦE
  obtain ⟨hchar, hnorm⟩ := exists_charTwo_map_of_canonical hS₀N hVK hKn hV2 hVc
    (fun s hs => hKinv _ ⟨s, hs, rfl⟩)
  have hKML : K.map L.subtype ≤ ML := hall _ (Subgroup.map_subtype_le K) hnorm hchar
  apply hKnot
  intro k hk
  have hkE : (k : G) ∈ Subgroup.normalizer (E : Set G) := hEnorm (hKML ⟨k, hk, rfl⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have := Subgroup.mem_normalizer_iff.mp hkE (h : G)
  exact this

end M2x

end CFSG.QuasithinUnique.Unc25G2
