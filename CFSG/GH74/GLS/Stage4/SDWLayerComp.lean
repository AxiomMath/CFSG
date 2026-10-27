module

public import CFSG.GH74.GLS.Stage4.SDWLayerFieldL
public import CFSG.GH74.GLS.Stage4.SDWLayerFieldU
public import CFSG.GH74.GLS.Stage4.T2P56Excl
public import CFSG.GH74.GLS.Stage4.T2P56bSyl
public import CFSG.Milestones.LR_semidihedral_simple_recognition
public import CFSG.Milestones.LR_wreathed_simple_recognition
public import CFSG.GH74.GLS.LU.Local.SL2Pure

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

@[expose] def SDWreathedComponent : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsKGroupNative X → pPrimeCore 2 X = ⊥ → HasSDOrWreathedSylow X →
    ∀ p n : ℕ, p.Prime → p ≠ 2 → 3 ≤ p ^ n → ∀ z : X, orderOf z = 2 →
      ∀ K : Subgroup X, z ∈ K → HasSL2Model ↥K (fun q => q = p ^ n) →
        (∀ c : X, c * z = z * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
          (∃ a : X, a * z * a⁻¹ ≠ z ∧ (a * z * a⁻¹) * z = z * (a * z * a⁻¹)) →
            ∃ E : Subgroup X, E.Normal ∧ K ≤ E ∧ Odd E.index ∧ IsSimpleGroup ↥E

section Facts

theorem hasSDOrWreathedSylow_normal_odd {X : Type} [Group X] [Finite X] {E : Subgroup X} [E.Normal]
    (hE : Odd E.index) (h : HasSDOrWreathedSylow X) : HasSDOrWreathedSylow ↥E := by
  obtain ⟨S, hS⟩ := h
  have hSE : (S : Subgroup X) ≤ E := sylow_le_of_odd_index' hE S
  have hiso : ↥((S.subtype hSE : Sylow 2 ↥E) : Subgroup ↥E) ≃* ↥(S : Subgroup X) := by
    rw [Sylow.coe_subtype]
    exact Subgroup.subgroupOfEquivOfLe hSE
  refine ⟨S.subtype hSE, ?_⟩
  rcases hS with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact Or.inl ⟨m, hm, ⟨hiso.trans e⟩⟩
  · exact Or.inr ⟨m, hm, ⟨hiso.trans e⟩⟩

theorem hasSL2Model_subgroupOf' {G : Type} [Group G] {X K : Subgroup G} (hKX : K ≤ X) {P : ℕ → Prop}
    (h : HasSL2Model ↥K P) : HasSL2Model ↥(K.subgroupOf X) P := by
  obtain ⟨F, iF, iFin, hF, ⟨e⟩⟩ := h
  exact ⟨F, iF, iFin, hF, ⟨(Subgroup.subgroupOfEquivOfLe hKX).trans e⟩⟩

theorem card_of_hasSL2Model {G : Type} [Group G] {K : Subgroup G} {q : ℕ}
    (h : HasSL2Model ↥K (fun q' => q' = q)) : Nat.card ↥K = q * (q ^ 2 - 1) := by
  obtain ⟨F, iF, iFin, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr (e.trans (specialLinearGroupEquivStatedSL 2 F).symm).toEquiv]
  have := t2C_card_sl2 (F := F)
  rw [this, hF]

theorem hasSL2Model_involution_central {G : Type} [Group G] {K : Subgroup G} {q : ℕ} (hq : Odd q)
    (h : HasSL2Model ↥K (fun q' => q' = q)) {z : G} (hzK : z ∈ K) (hzz : z * z = 1) :
    ∀ k ∈ K, k * z = z * k := by
  obtain ⟨F, iF, iFin, hF, ⟨e₀⟩⟩ := h
  let e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F := e₀.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hodd : Odd (Nat.card F) := by rw [hF]; exact hq
  have h2 : (2 : F) ≠ 0 := t2P56_two_ne_zero hodd
  have hsq : e ⟨z, hzK⟩ * e ⟨z, hzK⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 := Subtype.ext (by simpa using hzz)
    rw [this, map_one]
  have hcen := LU.Local.sl2_involution_central h2 hsq
  intro k hk
  have h' : e (⟨k, hk⟩ * ⟨z, hzK⟩) = e (⟨z, hzK⟩ * ⟨k, hk⟩) := by
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hcen (e ⟨k, hk⟩)
  exact congrArg Subtype.val (e.injective h')

end Facts

section Main

theorem sdwreathedLayer_of_component
    (hC : SDWreathedComponent) : SDWreathedLayer := by
  intro X _ _ hKX hbot hSyl p n hp hp2 hq z hz K hzK hK hCK hfus
  obtain ⟨E, hEn, hKE, hEodd, hEs⟩ := hC X hKX hbot hSyl p n hp hp2 hq z hz K hzK hK hCK hfus
  refine ⟨E, hEn, hKE, hEodd, ?_⟩
  have := hEs
  have hzE : z ∈ E := hKE hzK
  let z' : ↥E := ⟨z, hzE⟩
  have hz'2 : orderOf z' = 2 := by rw [← hz]; exact Subgroup.orderOf_mk z hzE
  have hzK' : z' ∈ K.subgroupOf E := hzK
  have hK' : HasSL2Model ↥(K.subgroupOf E) (fun q => q = p ^ n) := hasSL2Model_subgroupOf' hKE hK
  have hCK' : ∀ c : ↥E, c * z' = z' * c → ∀ k ∈ K.subgroupOf E, c * k * c⁻¹ ∈ K.subgroupOf E :=
    fun c hc k hk => hCK (c : X) (congrArg Subtype.val hc) (k : X) hk
  have hcardK : Nat.card ↥K = p ^ n * ((p ^ n) ^ 2 - 1) := card_of_hasSL2Model hK
  have hnonab : ∃ a b : ↥E, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative ↥E := ⟨⟨fun a b => hcon a b⟩⟩
    have hprime := Group.is_simple_iff_prime_card.1 hEs
    have hdvd : Nat.card ↥(K.subgroupOf E) ∣ Nat.card ↥E := Subgroup.card_subgroup_dvd_card _
    have hcardK' : Nat.card ↥(K.subgroupOf E) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv
    rw [hcardK', hcardK] at hdvd
    have hq3 : 3 ≤ p ^ n := hq
    have h1 : p ^ n ∣ Nat.card ↥E := (Dvd.intro _ rfl).trans hdvd
    have h2 : ((p ^ n) ^ 2 - 1) ∣ Nat.card ↥E := (Dvd.intro_left _ rfl).trans hdvd
    have hq2 : 9 ≤ (p ^ n) ^ 2 := by nlinarith
    rcases (Nat.dvd_prime hprime).1 h1 with h | h
    · omega
    · rcases (Nat.dvd_prime hprime).1 h2 with h' | h'
      · omega
      · have h3 : (p ^ n) ^ 2 = p ^ n + 1 := by omega
        nlinarith
  have hshape := hasSDOrWreathedSylow_normal_odd hEodd hSyl
  have hLn : ∀ {ε : ℤ} {p' f : ℕ}, p'.Prime → p' ≠ 2 → IsLnEps 3 ↥E ε (p' ^ f) →
      (ε = 1 ∨ ε = -1) → IsLnEps 3 ↥E ε (p ^ n) := by
    intro ε p' f hp' hp'2 hmodel hε
    have hfe : p' ^ f = p ^ n := by
      rcases hε with rfl | rfl
      · exact field_eq_of_component_L3 hp' hp'2 hmodel hp hp2 hK' hq hzK' hz'2 hCK'
      · exact field_eq_of_component_U3 hp' hp'2 hmodel hp hp2 hK' hq hzK' hz'2 hCK'
    rw [hfe] at hmodel
    exact hmodel
  have hM11 : Nonempty (↥E ≃* CFSG.Open.StatedM11) → p ^ n = 3 := by
    intro hM
    obtain ⟨hc48, -⟩ :=
      CFSG.Semidihedral.ProperSubgroupRegularity.stated_m11_involution_centralizer_card_and_core
        ↥E hM z' hz'2
    have hzz : z * z = 1 := by
      have h := pow_orderOf_eq_one z
      rw [hz, sq] at h
      exact h
    have hle : K.subgroupOf E ≤ Subgroup.centralizer ({z'} : Set ↥E) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact hasSL2Model_involution_central ((hp.odd_of_ne_two hp2).pow) hK hzK hzz (k : X) hk
    have hdvd := Subgroup.card_dvd_of_le hle
    have hcardK' : Nat.card ↥(K.subgroupOf E) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv
    rw [hcardK', hcardK] at hdvd
    have h48 : Nat.card ↥(Subgroup.centralizer ({z'} : Set ↥E)) = 48 := hc48
    rw [h48] at hdvd
    have hle48 := Nat.le_of_dvd (by norm_num) hdvd
    by_contra hne
    have h4 : 4 ≤ p ^ n := by
      have h3' : 3 ≤ p ^ n := hq
      omega
    obtain ⟨t, ht⟩ : ∃ t, (p ^ n) ^ 2 = t + 1 := ⟨(p ^ n) ^ 2 - 1, by
      have : 1 ≤ (p ^ n) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega⟩
    have ht15 : 15 ≤ t := by nlinarith
    rw [ht, Nat.add_sub_cancel] at hle48
    nlinarith
  rcases hasSDOrWreathedSylow_iff.1 hshape with ⟨S, m, hm, ⟨e⟩⟩ | ⟨S, m, hm, ⟨e⟩⟩
  · rcases CFSG.Milestones.lr_semidihedral_simple_recognition_1 ↥E hnonab ⟨S, m, hm, ⟨e⟩⟩ with
      ⟨p', f, hp', hp'2, -, -, hmodel⟩ | ⟨p', f, hp', hp'2, -, -, hmodel⟩ | hM
    · exact Or.inl ⟨1, Or.inl rfl, hLn hp' hp'2 (Or.inl ⟨rfl, hmodel.2⟩) (Or.inl rfl)⟩
    · exact Or.inl ⟨-1, Or.inr rfl, hLn hp' hp'2 (Or.inr ⟨rfl, hmodel.2⟩) (Or.inr rfl)⟩
    · exact Or.inr ⟨hM11 hM, hM⟩
  · rcases CFSG.Milestones.lr_wreathed_simple_recognition_1 ↥E hnonab ⟨S, m, hm, ⟨e⟩⟩ with
      ⟨p', f, hp', hp'2, -, -, hmodel⟩ | ⟨p', f, hp', hp'2, -, -, hmodel⟩
    · exact Or.inl ⟨1, Or.inl rfl, hLn hp' hp'2 (Or.inl ⟨rfl, hmodel.2⟩) (Or.inl rfl)⟩
    · exact Or.inl ⟨-1, Or.inr rfl, hLn hp' hp'2 (Or.inr ⟨rfl, hmodel.2⟩) (Or.inr rfl)⟩

end Main

end CFSG.GH74.GLS.Stage4.Rest
