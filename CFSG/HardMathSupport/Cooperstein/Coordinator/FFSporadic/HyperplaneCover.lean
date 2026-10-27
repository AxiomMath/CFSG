module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit
public import CFSG.RankThree.PartOne.KP.CentralCoverThree
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section Engine

variable {W : Type} [CommGroup W] [Finite W]

local instance : Finite (MulAut W) :=
  Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective

open scoped Classical in
theorem two_pow_le_card_ker_of_hyperplane_cover (hW : ∀ w : W, w * w = 1) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {U T : Subgroup (MulAut W)}
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUp : ∀ a ∈ U, a ^ p = 1)
    (hTU : T ≤ Subgroup.normalizer (U : Set (MulAut W))) {m : ℕ}
    (horb : ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p →
      ¬ T ≤ Subgroup.normalizer (D : Set (MulAut W)) →
      m ≤ (T ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex T)
    (hcore : ∃ u ∈ U, u ≠ 1 ∧ ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p →
      T ≤ Subgroup.normalizer (D : Set (MulAut W)) → u ∈ D) :
    2 ^ (m * orderOf (2 : ZMod p)) ≤ Nat.card (normHom U).ker := by
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hUodd : Odd (Nat.card U) := odd_card_of_pow_eq_one hodd hUp
  set K : Subgroup W := (normHom U).ker with hK
  have hKU : ∀ a ∈ U, ∀ k ∈ K, a k ∈ K := fun a ha k hk =>
    map_ker_normHom (Subgroup.le_normalizer ha) hk
  have hKT : ∀ t ∈ T, ∀ k ∈ K, t k ∈ K := fun t ht k hk => map_ker_normHom (hTU ht) hk
  have hfix : fixV U ⊓ K = ⊥ := fixV_inf_ker_normHom hW hUodd
  have : Fintype (Subgroup (MulAut W)) := Fintype.ofFinite _
  let 𝒟 : Finset (Subgroup (MulAut W)) :=
    Finset.univ.filter (fun D => D ≤ U ∧ D.relIndex U = p)
  have h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ U ∧ D.relIndex U = p := fun D => by simp [𝒟]
  obtain ⟨u, huU, hu1, hu⟩ := hcore
  obtain ⟨D₀, hD₀𝒟, hD₀ne, hD₀T⟩ : ∃ D ∈ 𝒟, fixV D ⊓ K ≠ ⊥ ∧
      ¬ T ≤ Subgroup.normalizer (D : Set (MulAut W)) := by
    by_contra hcon
    push Not at hcon
    apply hu1
    have hukK : ∀ k ∈ K, u k = k := by
      intro k hk
      obtain ⟨x, hx⟩ := hyperplaneHom_surjective hW hp2 hUc hUp hKU hfix 𝒟 h𝒟 hk
      rw [← hx, hyperplaneHom_apply, map_prod]
      refine Finset.prod_congr rfl fun D _ => ?_
      by_cases hD : fixV (D : Subgroup (MulAut W)) ⊓ K = ⊥
      · have hall : ∀ y : W, y ∈ fixV (D : Subgroup (MulAut W)) ⊓ K → y = 1 := fun y hy => by
          rw [hD] at hy
          exact Subgroup.mem_bot.1 hy
        rw [hall _ (x D).2, map_one]
      · obtain ⟨hDU, hDrel⟩ := (h𝒟 D).1 D.2
        exact mem_fixV.1 (Subgroup.mem_inf.1 (x D).2).1 u (hu D hDU hDrel (hcon D D.2 hD))
    apply DFunLike.ext
    intro w
    have hf : normHom U w ∈ fixV U := normHom_mem_fixV U w
    have hnf : normHom U (normHom U w) = normHom U w := normHom_of_mem_fixV hW hUodd hf
    have hkK : w * (normHom U w)⁻¹ ∈ K := by
      rw [hK, MonoidHom.mem_ker, map_mul, map_inv, hnf, mul_inv_cancel]
    have h1 := hukK _ hkK
    have h2 : (u : MulAut W) (normHom U w) = normHom U w := mem_fixV.1 hf u huU
    rw [map_mul, map_inv, h2] at h1
    exact mul_right_cancel h1
  have hcardK := card_eq_prod_card_fixV_inf_hyperplanes hW hp2 hUc hUp hKU hfix 𝒟 h𝒟
  obtain ⟨hD₀U, hD₀rel⟩ := (h𝒟 D₀).1 hD₀𝒟
  let 𝒟g : Finset (Subgroup (MulAut W)) := 𝒟.filter (fun D => fixV D ⊓ K ≠ ⊥)
  have hD₀cardpos : 0 < Nat.card D₀ := Nat.card_pos
  have hpD₀ : p * Nat.card D₀ = Nat.card U := by
    have := D₀.relIndex_mul_card U
    rwa [hD₀rel, inf_eq_left.2 hD₀U] at this
  have hconj : ∀ t ∈ T, CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.conjSub t D₀ ∈ 𝒟g := by
    intro t ht
    have htN := hTU ht
    have hle : CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.conjSub t D₀ ≤ U := by
      intro x hx
      rw [CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.mem_conjSub] at hx
      have h1 := hD₀U hx
      have := (Subgroup.mem_set_normalizer_iff.1 htN (t⁻¹ * x * t)).1 h1
      have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
      rwa [e] at this
    have hrel : (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.conjSub t D₀).relIndex U = p := by
      have h1 := (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.conjSub t D₀).relIndex_mul_card U
      rw [inf_eq_left.2 hle, CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.card_conjSub] at h1
      exact Nat.eq_of_mul_eq_mul_right hD₀cardpos (h1.trans hpD₀.symm)
    refine Finset.mem_filter.2 ⟨(h𝒟 _).2 ⟨hle, hrel⟩, ?_⟩
    obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD₀ne
    obtain ⟨hkD, hkK⟩ := Subgroup.mem_inf.1 hk
    apply Subgroup.ne_bot_iff_exists_ne_one.2
    refine ⟨⟨t k, Subgroup.mem_inf.2 ⟨?_, hKT t ht k hkK⟩⟩, ?_⟩
    · rw [mem_fixV]
      intro x hx
      rw [CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.mem_conjSub] at hx
      have hcomm : x * t = t * (t⁻¹ * x * t) := by group
      have hy : (t⁻¹ * x * t) k = k := mem_fixV.1 hkD _ hx
      calc x (t k) = (x * t) k := rfl
        _ = (t * (t⁻¹ * x * t)) k := by rw [hcomm]
        _ = t ((t⁻¹ * x * t) k) := rfl
        _ = t k := by rw [hy]
    · intro h1
      apply hk1
      have h2 : (t : MulAut W) k = 1 := congrArg Subtype.val h1
      apply Subtype.ext
      show k = 1
      have : (t : MulAut W) k = (t : MulAut W) 1 := by rw [h2, map_one]
      exact (t : MulAut W).injective this
  have hm : m ≤ 𝒟g.card :=
    (horb D₀ hD₀U hD₀rel hD₀T).trans (relIndex_le_card_of_conj hconj)
  have hfac : ∀ D ∈ 𝒟g, 2 ^ orderOf (2 : ZMod p) ≤ Nat.card ↥(fixV D ⊓ K) := by
    intro D hD
    obtain ⟨hD𝒟, hDne⟩ := Finset.mem_filter.1 hD
    obtain ⟨hDU, hDrel⟩ := (h𝒟 D).1 hD𝒟
    exact two_pow_le_card_fixV_inf hW hUc hUp hKU hfix hDU hDrel hDne
  have hpos : ∀ D ∈ 𝒟, 0 < Nat.card ↥(fixV D ⊓ K) := fun D _ => Nat.card_pos
  calc 2 ^ (m * orderOf (2 : ZMod p)) = (2 ^ orderOf (2 : ZMod p)) ^ m := by
        rw [mul_comm, pow_mul]
    _ ≤ (2 ^ orderOf (2 : ZMod p)) ^ 𝒟g.card :=
        Nat.pow_le_pow_right (Nat.one_le_two_pow) hm
    _ = ∏ _D ∈ 𝒟g, 2 ^ orderOf (2 : ZMod p) := by rw [Finset.prod_const]
    _ ≤ ∏ D ∈ 𝒟g, Nat.card ↥(fixV D ⊓ K) := Finset.prod_le_prod hfac
    _ ≤ (∏ D ∈ 𝒟g, Nat.card ↥(fixV D ⊓ K)) *
          ∏ D ∈ 𝒟.filter (fun D => ¬ (fixV D ⊓ K ≠ ⊥)), Nat.card ↥(fixV D ⊓ K) :=
        Nat.le_mul_of_pos_right _ (Finset.prod_pos fun D hD => hpos D (Finset.mem_filter.1 hD).1)
    _ = ∏ D ∈ 𝒟, Nat.card ↥(fixV D ⊓ K) := Finset.prod_filter_mul_prod_filter_not 𝒟 (fun D => fixV D ⊓ K ≠ ⊥)
        (fun D => Nat.card ↥(fixV D ⊓ K))
    _ = Nat.card K := hcardK.symm

theorem two_pow_le_card_of_hyperplane_cover (hW : ∀ w : W, w * w = 1) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {U T : Subgroup (MulAut W)}
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUp : ∀ a ∈ U, a ^ p = 1)
    (hTU : T ≤ Subgroup.normalizer (U : Set (MulAut W))) {m : ℕ}
    (horb : ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p →
      ¬ T ≤ Subgroup.normalizer (D : Set (MulAut W)) →
      m ≤ (T ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex T)
    (hcore : ∃ u ∈ U, u ≠ 1 ∧ ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p →
      T ≤ Subgroup.normalizer (D : Set (MulAut W)) → u ∈ D) :
    2 ^ (m * orderOf (2 : ZMod p)) ≤ Nat.card W :=
  (two_pow_le_card_ker_of_hyperplane_cover hW hp2 hUc hUp hTU horb hcore).trans
    (Subgroup.card_le_card_group _)

end Engine

section Cover

variable {W : Type} [CommGroup W] [Finite W]

local instance : Finite (MulAut W) :=
  Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] {T D : Subgroup G}
    (h : ∀ t ∈ T, ∀ x ∈ D, t * x * t⁻¹ ∈ D) : T ≤ Subgroup.normalizer (D : Set G) := by
  intro t ht
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨fun hx => h t ht x hx, fun hx => ?_⟩
  have := h t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

theorem conj_mem_of_le_normalizer {G : Type*} [Group G] {T D : Subgroup G}
    (h : T ≤ Subgroup.normalizer (D : Set G)) {t : G} (ht : t ∈ T) {x : G} (hx : x ∈ D) :
    t * x * t⁻¹ ∈ D :=
  (Subgroup.mem_set_normalizer_iff.1 (h ht) x).1 hx

private theorem card_sup_mul_card_inf_of_normal' {G : Type*} [Group G] (A L : Subgroup G)
    [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) =
      Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal' (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem card_sup_mul_card_inf_of_comm {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  refine card_sup_mul_card_inf_of_le_normalizer fun b hb => ?_
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  have hc : ∀ a ∈ A, b * a * b⁻¹ = a := fun a ha => by
    rw [← h a ha b hb]; group
  have hinv : ∀ a ∈ A, b⁻¹ * a * b = a := fun a ha => by
    have hba : b * a = a * b := (h a ha b hb).symm
    calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
      _ = a := by rw [← hba]; group
  refine ⟨fun hx => by rw [hc x hx]; exact hx, fun hx => ?_⟩
  have hx' : x = b⁻¹ * (b * x * b⁻¹) * b := by group
  rw [hx', hinv _ hx]
  exact hx

theorem map_conj_le_of_conj_mem {G : Type*} [Group G] {X : Subgroup G} {t : G}
    (hX : ∀ x ∈ X, t * x * t⁻¹ ∈ X) : X.map (MulAut.conj t).toMonoidHom ≤ X := by
  rintro _ ⟨y, hy, rfl⟩
  simpa [MulAut.conj_apply] using hX y hy

theorem exists_mem_invariant_hyperplanes_of_cover {p : ℕ} [Fact p.Prime]
    {U Z T : Subgroup (MulAut W)} (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hZU : Z ≤ U)
    (hZ : Nat.card Z = p) (hpU : p < Nat.card U) (hTZ : ∀ t ∈ T, ∀ z ∈ Z, t * z * t⁻¹ ∈ Z)
    (hnoZ : ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p →
      T ≤ Subgroup.normalizer (D : Set (MulAut W)) → ¬ Z ≤ D) :
    ∃ u ∈ U, u ≠ 1 ∧ ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p →
      T ≤ Subgroup.normalizer (D : Set (MulAut W)) → u ∈ D := by
  classical
  have hp := (Fact.out : p.Prime)
  have hcardD : ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p →
      p * Nat.card D = Nat.card U := fun D hDU hD => by
    have := D.relIndex_mul_card U
    rwa [hD, inf_eq_left.2 hDU] at this
  have hZD : ∀ D : Subgroup (MulAut W), ¬ Z ≤ D → Z ⊓ D = ⊥ := by
    intro D hD
    have hdvd : Nat.card ↥(Z ⊓ D) ∣ Nat.card Z := Subgroup.card_dvd_of_le inf_le_left
    rw [hZ] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      apply hD
      have : Z ⊓ D = Z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hZ])
      rw [← this]
      exact inf_le_right
  have huniq : ∀ D₁ D₂ : Subgroup (MulAut W), D₁ ≤ U → D₁.relIndex U = p →
      T ≤ Subgroup.normalizer (D₁ : Set (MulAut W)) → D₂ ≤ U → D₂.relIndex U = p →
      T ≤ Subgroup.normalizer (D₂ : Set (MulAut W)) → D₁ = D₂ := by
    intro D₁ D₂ h1U h1p h1T h2U h2p h2T
    by_contra hne
    have hsup : D₁ ⊔ D₂ = U := sup_eq_of_relIndex_eq_prime h1U h2U h1p h2p hne
    have hc12 : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb =>
      hUc a (h1U ha) b (h2U hb)
    have e1 := card_sup_mul_card_inf_of_comm hc12
    rw [hsup] at e1
    have c1 := hcardD D₁ h1U h1p
    have c2 := hcardD D₂ h2U h2p
    have e2 : p * Nat.card ↥(D₁ ⊓ D₂) = Nat.card D₂ := by
      have hpos : 0 < Nat.card D₁ := Nat.card_pos
      rw [← c1] at e1
      apply Nat.eq_of_mul_eq_mul_left hpos
      nlinarith [e1]
    have hZ12 : Z ⊓ (D₁ ⊓ D₂) = ⊥ :=
      le_bot_iff.1 ((hZD D₁ (hnoZ D₁ h1U h1p h1T)) ▸ inf_le_inf_left Z inf_le_left)
    have hc3 : ∀ a ∈ D₁ ⊓ D₂, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
      hUc a (h1U ha.1) b (hZU hb)
    have e3 := card_sup_mul_card_inf_of_comm hc3
    rw [show (D₁ ⊓ D₂) ⊓ Z = Z ⊓ (D₁ ⊓ D₂) from inf_comm _ _, hZ12, Subgroup.card_bot, hZ] at e3
    have hD₃U : (D₁ ⊓ D₂) ⊔ Z ≤ U := sup_le (inf_le_left.trans h1U) hZU
    have hD₃card : Nat.card ↥((D₁ ⊓ D₂) ⊔ Z) = Nat.card D₂ := by
      rw [← e2]
      linarith [e3]
    have hD₃p : ((D₁ ⊓ D₂) ⊔ Z).relIndex U = p := by
      have h := ((D₁ ⊓ D₂) ⊔ Z).relIndex_mul_card U
      rw [inf_eq_left.2 hD₃U, hD₃card] at h
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.trans (hcardD D₂ h2U h2p).symm)
    have hD₃T : T ≤ Subgroup.normalizer (((D₁ ⊓ D₂) ⊔ Z : Subgroup (MulAut W)) : Set (MulAut W)) := by
      refine le_normalizer_of_conj_mem fun t ht x hx => ?_
      have hmap : ((D₁ ⊓ D₂) ⊔ Z).map (MulAut.conj t).toMonoidHom ≤ (D₁ ⊓ D₂) ⊔ Z := by
        rw [Subgroup.map_sup]
        refine sup_le_sup (map_conj_le_of_conj_mem fun y hy => ⟨?_, ?_⟩)
          (map_conj_le_of_conj_mem fun z hz => hTZ t ht z hz)
        · exact conj_mem_of_le_normalizer h1T ht hy.1
        · exact conj_mem_of_le_normalizer h2T ht hy.2
      exact hmap ⟨x, hx, by simp [MulAut.conj_apply]⟩
    exact hnoZ _ hD₃U hD₃p hD₃T le_sup_right
  by_cases hex : ∃ D : Subgroup (MulAut W), D ≤ U ∧ D.relIndex U = p ∧
      T ≤ Subgroup.normalizer (D : Set (MulAut W))
  · obtain ⟨D, hDU, hDp, hDT⟩ := hex
    have hDne : D ≠ ⊥ := by
      intro h
      have := hcardD D hDU hDp
      rw [h, Subgroup.card_bot, mul_one] at this
      omega
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hDne
    refine ⟨u, hDU hu, fun h => hu1 (Subtype.ext h), fun D' hD'U hD'p hD'T => ?_⟩
    rw [huniq D' D hD'U hD'p hD'T hDU hDp hDT]
    exact hu
  · push Not at hex
    have hUne : U ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hpU
      exact absurd hpU (by have := hp.two_le; omega)
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUne
    exact ⟨u, hu, fun h => hu1 (Subtype.ext h), fun D hDU hDp hDT => absurd hDT (hex D hDU hDp)⟩

end Cover

section CoverAbelian

open CFSG.RankThree.PartOne.CentralCoverThree
open scoped commutatorElement IsMulCommutative

theorem even_finrank_of_alt_pairing {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (f : V → V → ZMod p)
    (hl : ∀ u u' w, f (u + u') w = f u w + f u' w) (hr : ∀ u w w', f u (w + w') = f u w + f u w')
    (halt : ∀ u, f u u = 0) (hnd : ∀ u, (∀ w, f u w = 0) → u = 0) :
    Even (Module.finrank (ZMod p) V) := by
  let gL : V → V →+ ZMod p := fun w => AddMonoidHom.mk' (fun u => f u w) (fun u u' => hl u u' w)
  let gR : V → V →+ ZMod p := fun u => AddMonoidHom.mk' (fun w => f u w) (fun w w' => hr u w w')
  let B : LinearMap.BilinForm (ZMod p) V :=
    LinearMap.mk₂ (ZMod p) f hl (fun c u w => ZMod.map_smul (gL w) c u) hr
      (fun c u w => ZMod.map_smul (gR u) c w)
  have hB : ∀ u w, B u w = f u w := fun u w => rfl
  have hA : B.IsAlt := fun u => by rw [hB]; exact halt u
  have hswap : ∀ u w, f w u = - f u w := fun u w => by
    have h := halt (u + w)
    rw [hl, hr, hr, halt u, halt w] at h
    linear_combination h
  have hndB : B.Nondegenerate := by
    refine ⟨fun u hu => hnd u fun w => ?_, fun w hw => hnd w fun u => ?_⟩
    · rw [← hB]; exact hu w
    · rw [hswap, ← hB, hw u, neg_zero]
  exact LinearMap.BilinForm.IsAlt.even_finrank hA hndB

theorem false_of_center_le {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
    (Z₀ : Subgroup Y) (hZc : Z₀ ≤ Subgroup.center Y) (hZ : Nat.card Z₀ = p)
    (hcomm : ∀ a b : Y, ⁅a, b⁆ ∈ Z₀) (hpow : ∀ a : Y, a ^ p ∈ Z₀)
    (hcen : Subgroup.center Y ≤ Z₀) {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card Y = p ^ (2 * n)) :
    False := by
  classical
  have hp := (Fact.out : p.Prime)
  have : Z₀.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.1 (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  let φ : Y →* Y ⧸ Z₀ := QuotientGroup.mk' Z₀
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective Z₀
  have hker : φ.ker ≤ Subgroup.center Y := by
    rw [QuotientGroup.ker_mk']
    exact hZc
  have hea : IsElementaryAbelian p (Y ⧸ Z₀) :=
    { toIsMulCommutative := ⟨⟨fun a b => by
        induction a using QuotientGroup.induction_on with | _ x
        induction b using QuotientGroup.induction_on with | _ y
        have h1 : ⁅φ x, φ y⁆ = 1 := by
          rw [← map_commutatorElement]
          exact (QuotientGroup.eq_one_iff _).2 (hcomm x y)
        exact commutatorElement_eq_one_iff_mul_comm.1 h1⟩⟩
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_of_forall_pow_eq_one fun q => ?_
        induction q using QuotientGroup.induction_on with | _ x
        rw [← QuotientGroup.mk_pow]
        exact (QuotientGroup.eq_one_iff _).2 (hpow x) }
  let cc : (Y ⧸ Z₀) → (Y ⧸ Z₀) → Y := fun a b => ⁅Function.surjInv hφ a, Function.surjInv hφ b⁆
  have hcc : ∀ y z : Y, ⁅y, z⁆ = cc (φ y) (φ z) := fun y z =>
    commutator_eq_of_map_eq hker (Function.surjInv_eq hφ _).symm (Function.surjInv_eq hφ _).symm
  have hccZ : ∀ a b, cc a b ∈ Z₀ := fun a b => hcomm _ _
  let ccZ : (Y ⧸ Z₀) → (Y ⧸ Z₀) → Z₀ := fun a b => ⟨cc a b, hccZ a b⟩
  have hmul_left : ∀ a a' b, ccZ (a * a') b = ccZ a b * ccZ a' b := by
    intro a a' b
    apply Subtype.ext
    obtain ⟨y, rfl⟩ := hφ a
    obtain ⟨y', rfl⟩ := hφ a'
    obtain ⟨z, rfl⟩ := hφ b
    show cc (φ y * φ y') (φ z) = cc (φ y) (φ z) * cc (φ y') (φ z)
    rw [← map_mul, ← hcc, ← hcc, ← hcc]
    exact commutator_mul_left_of_central (hZc (hcomm y' z))
  have hmul_right : ∀ a b b', ccZ a (b * b') = ccZ a b * ccZ a b' := by
    intro a b b'
    apply Subtype.ext
    obtain ⟨y, rfl⟩ := hφ a
    obtain ⟨z, rfl⟩ := hφ b
    obtain ⟨z', rfl⟩ := hφ b'
    show cc (φ y) (φ z * φ z') = cc (φ y) (φ z) * cc (φ y) (φ z')
    rw [← map_mul, ← hcc, ← hcc, ← hcc]
    exact commutator_mul_right_of_central (hZc (hcomm y z'))
  have hself : ∀ a, ccZ a a = 1 := by
    intro a
    apply Subtype.ext
    obtain ⟨y, rfl⟩ := hφ a
    show cc (φ y) (φ y) = 1
    rw [← hcc]
    exact commutatorElement_self y
  obtain ⟨e⟩ : Nonempty (Z₀ ≃* Multiplicative (ZMod p)) :=
    ⟨mulEquivOfPrimeCardEq hZ (by simp)⟩
  let ℓ : Z₀ → ZMod p := fun z => Multiplicative.toAdd (e z)
  have hℓmul : ∀ z z', ℓ (z * z') = ℓ z + ℓ z' := fun z z' => by simp [ℓ]
  have hℓinj : ∀ z, ℓ z = 0 → z = 1 := fun z hz => by
    apply e.injective
    simpa [ℓ] using hz
  have hℓone : ℓ 1 = 0 := by simp [ℓ]
  have heven := even_finrank_of_alt_pairing (p := p) (V := Additive (Y ⧸ Z₀))
    (fun u w => ℓ (ccZ (Additive.toMul u) (Additive.toMul w)))
    (fun u u' w => by
      show ℓ (ccZ (Additive.toMul u * Additive.toMul u') _) = _
      rw [hmul_left, hℓmul])
    (fun u w w' => by
      show ℓ (ccZ _ (Additive.toMul w * Additive.toMul w')) = _
      rw [hmul_right, hℓmul])
    (fun u => by rw [hself, hℓone])
    (fun u hu => by
      have hx := Function.surjInv_eq hφ (Additive.toMul u)
      set x := Function.surjInv hφ (Additive.toMul u)
      have hxc : x ∈ Subgroup.center Y := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h1 := hℓinj _ (hu (Additive.ofMul (φ y)))
        have h2 : ccZ (Additive.toMul u) (φ y) = 1 := h1
        have h3 : ⁅x, y⁆ = 1 := by
          rw [hcc, hx]
          exact congrArg Subtype.val h2
        exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
      have hx0 : φ x = 1 := (QuotientGroup.eq_one_iff _).2 (hcen hxc)
      rw [hx] at hx0
      exact Additive.toMul.injective hx0)
  have hcardV : Nat.card (Additive (Y ⧸ Z₀)) = p ^ (2 * n - 1) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z₀
    rw [hcard, hZ] at h1
    have h2 : Nat.card (Y ⧸ Z₀) = p ^ (2 * n - 1) := by
      have : p ^ (2 * n) = p ^ (2 * n - 1) * p := by
        rw [← pow_succ]; congr 1; omega
      rw [this] at h1
      exact (Nat.eq_of_mul_eq_mul_right hp.pos h1).symm
    exact h2
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod] at hcardV
  have hfin : Module.finrank (ZMod p) (Additive (Y ⧸ Z₀)) = 2 * n - 1 :=
    Nat.pow_right_injective hp.two_le hcardV
  obtain ⟨r, hr⟩ := heven
  omega

theorem commutative_exponent_of_cover {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {F Z T : Subgroup G} (hZF : Z ≤ F) (hZc : ∀ z ∈ Z, ∀ f ∈ F, f * z = z * f)
    (hZ : Nat.card Z = p) (hcomm : ∀ a ∈ F, ∀ b ∈ F, ⁅a, b⁆ ∈ Z) (hpow : ∀ a ∈ F, a ^ p ∈ Z)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = p ^ (2 * n))
    (hT : ∀ t ∈ T, ∀ f ∈ F, t * f * t⁻¹ ∈ F) (hTi : ∀ t ∈ T, t⁻¹ ∈ T)
    (hirr : ∀ R : Subgroup G, Z ≤ R → R ≤ F → (∀ t ∈ T, ∀ r ∈ R, t * r * t⁻¹ ∈ R) →
      R = Z ∨ R = F) :
    (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) ∧ ∀ a ∈ F, a ^ p = 1 := by
  classical
  have hp := (Fact.out : p.Prime)
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp.pos _).ne')
  let C : Subgroup G := (Subgroup.center ↥F).map F.subtype
  have hCF : C ≤ F := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hZC : Z ≤ C := fun z hz =>
    ⟨⟨z, hZF hz⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (hZc z hz y y.2), rfl⟩
  have hCcomm : ∀ c ∈ C, ∀ f ∈ F, c * f = f * c := by
    rintro _ ⟨x, hx, rfl⟩ f hf
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨f, hf⟩).symm
  have hCT : ∀ t ∈ T, ∀ c ∈ C, t * c * t⁻¹ ∈ C := by
    intro t ht c hc
    have hcF := hCF hc
    refine ⟨⟨t * c * t⁻¹, hT t ht c hcF⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
    have h1 := hCcomm c hc (t⁻¹ * y * t) (by
      have := hT t⁻¹ (hTi t ht) y y.2
      simpa using this)
    show (y : G) * (t * c * t⁻¹) = t * c * t⁻¹ * y
    calc (y : G) * (t * c * t⁻¹) = t * ((t⁻¹ * y * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * y * t)) * t⁻¹ := by rw [h1]
      _ = t * c * t⁻¹ * y := by group
  have hC : C = Z ∨ C = F := hirr C hZC hCF hCT
  have hcomm' : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    rcases hC with hC | hC
    · exfalso
      refine false_of_center_le (p := p) (Z.subgroupOf F) ?_ ?_ ?_ ?_ ?_ (n := n) (by omega)
        hcard
      · intro z hz
        exact Subgroup.mem_center_iff.2 fun y =>
          Subtype.ext (hZc z hz y y.2)
      · rw [← hZ]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZF).toEquiv
      · intro a b
        exact hcomm a a.2 b b.2
      · intro a
        exact hpow a a.2
      · intro x hx
        have : (x : G) ∈ C := ⟨x, hx, rfl⟩
        rw [hC] at this
        exact this
    · intro a ha b hb
      rw [← hC] at ha
      exact hCcomm a ha b hb
  refine ⟨hcomm', ?_⟩
  have hZpow : ∀ z ∈ Z, z ^ p = 1 := by
    intro z hz
    have : (⟨z, hz⟩ : ↥Z) ^ p = 1 := by
      rw [← hZ]
      exact pow_card_eq_one'
    simpa using congrArg Subtype.val this
  let P : Subgroup G :=
    { carrier := {a | a ∈ F ∧ a ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨F.mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hcomm' a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨F.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨F.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hPmem : ∀ a, a ∈ P ↔ a ∈ F ∧ a ^ p = 1 := fun _ => Iff.rfl
  have hZP : Z ≤ P := fun z hz => ⟨hZF hz, hZpow z hz⟩
  have hPF : P ≤ F := fun a ha => ha.1
  have hPT : ∀ t ∈ T, ∀ r ∈ P, t * r * t⁻¹ ∈ P := by
    intro t ht r hr
    refine ⟨hT t ht r ((hPmem r).1 hr).1, ?_⟩
    rw [conj_pow, ((hPmem r).1 hr).2]
    group
  rcases hirr P hZP hPF hPT with hP | hP
  · exfalso
    let ρ : ↥F →* ↥F := MonoidHom.mk' (fun a => a ^ p) (fun a b => by
      apply Subtype.ext
      show ((a * b : ↥F) : G) ^ p = _
      rw [Subgroup.coe_mul, (show Commute (a : G) (b : G) from hcomm' a a.2 b b.2).mul_pow]
      rfl)
    have hker : ρ.ker ≤ Z.subgroupOf F := by
      intro a ha
      have h1 : (a : G) ^ p = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 ha)
        simpa [ρ] using this
      have : (a : G) ∈ P := ⟨a.2, h1⟩
      rw [hP] at this
      exact this
    have hrange : ρ.range ≤ Z.subgroupOf F := by
      rintro _ ⟨a, rfl⟩
      exact hpow a a.2
    have hc1 : Nat.card (Z.subgroupOf F) = p := by
      rw [← hZ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZF).toEquiv
    have h2 := Subgroup.card_ker_mul_card_range ρ
    have h3 : Nat.card ρ.ker ≤ p := hc1 ▸ Subgroup.card_le_of_le hker
    have h4 : Nat.card ρ.range ≤ p := hc1 ▸ Subgroup.card_le_of_le hrange
    have h5 : p ^ (2 * n) ≤ p * p := by
      rw [← hcard, ← h2]
      exact Nat.mul_le_mul h3 h4
    have h6 : p ^ 2 < p ^ (2 * n) :=
      Nat.pow_lt_pow_right hp.one_lt (by omega)
    nlinarith [h5, h6]
  · intro a ha
    rw [← hP] at ha
    exact (hPmem a).1 ha |>.2

end CoverAbelian

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
