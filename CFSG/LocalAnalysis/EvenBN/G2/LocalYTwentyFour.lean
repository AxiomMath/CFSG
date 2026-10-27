module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentyThree

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

theorem mul_self_mem_of_sup {A B N : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hN : A ⊔ B ≤ normalizer (N : Set G)) (hA : ∀ a ∈ A, a * a ∈ N) (hB : ∀ b ∈ B, b * b ∈ N)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ N) :
    (∀ x ∈ A ⊔ B, x * x ∈ N) ∧ ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y * x⁻¹ * y⁻¹ ∈ N := by
  have hsq : ∀ x ∈ A ⊔ B, x * x ∈ N := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer' hAB x hx
    rw [show a * b * (a * b) = a * a * (a⁻¹ * b * a⁻¹⁻¹ * b⁻¹) * (b * b) by group]
    exact mul_mem (mul_mem (hA a ha) (hc _ (inv_mem ha) b hb)) (hB b hb)
  refine ⟨hsq, fun x hx y hy => ?_⟩
  rw [show x * y * x⁻¹ * y⁻¹ = x * y * (x * y) * (y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) * (y * y)⁻¹ by group]
  exact mul_mem (mul_mem (hsq _ (mul_mem hx hy))
    ((mem_normalizer_iff.1 (inv_mem (hN hy)) _).1 (inv_mem (hsq x hx)))) (inv_mem (hsq y hy))

theorem conj_mul_inv_mem_of_regular {A V E J : Subgroup G} {c : G} (hAE : A ≤ E)
    (hE : ∀ e ∈ E, ∃ a ∈ A, ∃ v ∈ V, e = a * v) (hEV : E ≤ normalizer (V : Set G))
    (hAV : A ⊓ V = ⊥) (hJA : J ≤ normalizer (A : Set G)) (hJV : J ≤ normalizer (V : Set G))
    (hJ : ∀ j ∈ J, ∀ k ∈ J, j * k = k * j) (hodd : Odd (Nat.card J))
    (htrans : ∀ x ∈ A, x ≠ 1 → ∀ y ∈ A, y ≠ 1 → ∃ j ∈ J, j * x * j⁻¹ = y)
    (hreg : ∀ x ∈ A, x ≠ 1 → ∀ j ∈ J, j * x = x * j → j = 1)
    (hcE : c ∈ normalizer (E : Set G)) (hcV : c ∈ normalizer (V : Set G))
    (hcJ : c ∈ centralizer (J : Set G)) {m : ℕ} (hcm : c ^ 2 ^ m = 1) :
    ∀ e ∈ E, c * e * c⁻¹ * e⁻¹ ∈ V := by
  have hconj : ∀ x y : G, x * y = y * x → ∀ z : G,
      x * (y * z * y⁻¹) * x⁻¹ = y * (x * z * x⁻¹) * y⁻¹ := fun x y hxy z => by
    calc x * (y * z * y⁻¹) * x⁻¹ = x * y * z * (x * y)⁻¹ := by group
      _ = y * x * z * (y * x)⁻¹ := by rw [hxy]
      _ = y * (x * z * x⁻¹) * y⁻¹ := by group
  have hmemAV : ∀ x ∈ A, x ∈ V → x = 1 := fun x hxA hxV => by
    have : x ∈ A ⊓ V := Subgroup.mem_inf.2 ⟨hxA, hxV⟩
    rwa [hAV, Subgroup.mem_bot] at this
  have hkey : ∀ a ∈ A, a⁻¹ * (c * a * c⁻¹) ∈ V := by
    by_cases hA : ∃ a₀ ∈ A, a₀ ≠ 1
    · obtain ⟨a₀, ha₀, ha₀1⟩ := hA
      obtain ⟨a₁, ha₁, v₁, hv₁, e₁⟩ := hE _ ((mem_normalizer_iff.1 hcE _).1 (hAE ha₀))
      have ha₁1 : a₁ ≠ 1 := by
        rintro rfl
        rw [one_mul] at e₁
        refine ha₀1 (hmemAV a₀ ha₀ ?_)
        have hv : c * a₀ * c⁻¹ ∈ V := by
          rw [e₁]
          exact hv₁
        have := (mem_normalizer_iff.1 (inv_mem hcV) _).1 hv
        rwa [show c⁻¹ * (c * a₀ * c⁻¹) * c⁻¹⁻¹ = a₀ by group] at this
      obtain ⟨j, hj, hja⟩ := htrans a₀ ha₀ ha₀1 a₁ ha₁ ha₁1
      have hstar : ∀ a ∈ A, (j * a * j⁻¹)⁻¹ * (c * a * c⁻¹) ∈ V := fun a ha => by
        by_cases ha1 : a = 1
        · simp [ha1]
        obtain ⟨k, hk, rfl⟩ := htrans a₀ ha₀ ha₀1 a ha ha1
        have hck : c * k = k * c := ((mem_centralizer_iff.1 hcJ) k hk).symm
        rw [hconj j k (hJ j hj k hk), hconj c k hck, hja, e₁,
          show (k * a₁ * k⁻¹)⁻¹ * (k * (a₁ * v₁) * k⁻¹) = k * v₁ * k⁻¹ by group]
        exact (mem_normalizer_iff.1 (hJV hk) _).1 hv₁
      have hiter : ∀ n : ℕ, ∀ a ∈ A,
          (j ^ n * a * (j ^ n)⁻¹)⁻¹ * (c ^ n * a * (c ^ n)⁻¹) ∈ V := by
        intro n
        induction n with
        | zero => intro a _; simp
        | succ n ih =>
          intro a ha
          have ha' : j ^ n * a * (j ^ n)⁻¹ ∈ A :=
            (mem_normalizer_iff.1 (hJA (pow_mem hj n)) _).1 ha
          rw [pow_succ', pow_succ', show (j * j ^ n * a * (j * j ^ n)⁻¹)⁻¹ *
            (c * c ^ n * a * (c * c ^ n)⁻¹) = (j * (j ^ n * a * (j ^ n)⁻¹) * j⁻¹)⁻¹ *
              (c * (j ^ n * a * (j ^ n)⁻¹) * c⁻¹) *
              (c * ((j ^ n * a * (j ^ n)⁻¹)⁻¹ * (c ^ n * a * (c ^ n)⁻¹)) * c⁻¹) by group]
          exact mul_mem (hstar _ ha') ((mem_normalizer_iff.1 hcV _).1 (ih a ha))
      have hjn : j ^ 2 ^ m = 1 := by
        have h1 := hiter (2 ^ m) a₀ ha₀
        simp only [hcm, one_mul, inv_one, mul_one] at h1
        have h2 : (j ^ 2 ^ m * a₀ * (j ^ 2 ^ m)⁻¹)⁻¹ * a₀ = 1 := hmemAV _
          (mul_mem (inv_mem ((mem_normalizer_iff.1 (hJA (pow_mem hj _)) _).1 ha₀)) ha₀) h1
        rw [inv_mul_eq_one] at h2
        refine hreg a₀ ha₀ ha₀1 _ (pow_mem hj _) ?_
        calc j ^ 2 ^ m * a₀ = j ^ 2 ^ m * a₀ * (j ^ 2 ^ m)⁻¹ * j ^ 2 ^ m := by group
          _ = a₀ * j ^ 2 ^ m := by rw [h2]
      have hj1 : j = 1 := by
        have hdvd2 : orderOf j ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hjn
        have hdvdJ : orderOf j ∣ Nat.card J := Subgroup.orderOf_dvd_natCard J hj
        have hcop : Nat.Coprime (2 ^ m) (Nat.card J) :=
          Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hodd)
        exact orderOf_eq_one_iff.1
          (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd2 hcop) hdvdJ)
      subst hj1
      intro a ha
      simpa using hstar a ha
    · intro a ha
      have ha1 : a = 1 := by
        by_contra ha1
        exact hA ⟨a, ha, ha1⟩
      simp [ha1]
  intro e he
  obtain ⟨a, ha, v, hv, rfl⟩ := hE e he
  rw [show c * (a * v) * c⁻¹ * (a * v)⁻¹ =
    a * (a⁻¹ * (c * a * c⁻¹) * (c * v * c⁻¹) * v⁻¹) * a⁻¹ by group]
  exact (mem_normalizer_iff.1 (hEV (hAE ha)) _).1
    (mul_mem (mul_mem (hkey a ha) ((mem_normalizer_iff.1 hcV _).1 hv)) (inv_mem hv))

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Light

theorem mem_of_mem_sup_zpowers_of_le (h : Setup G L f t) {A : Subgroup G}
    (htA : t ∈ normalizer (A : Set G)) (hAC : A ⊓ centralizer ({t} : Set G) ≤ L) {x : G}
    (hxL : x ∈ L) (hx : x ∈ A ⊔ zpowers t) : x ∈ A := by
  rcases (mem_sup_zpowers_iff_of h.t_mul_t htA).1 hx with h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    have hta : a = a * t * t := by rw [mul_assoc, h.t_mul_t, mul_one]
    have hat : a ∈ centralizer ({t} : Set G) := by
      rw [hta]
      exact mul_mem (h.L_le_centralizer hxL) (mem_centralizer_singleton_iff.2 rfl)
    have := mul_mem (inv_mem (hAC (Subgroup.mem_inf.2 ⟨ha, hat⟩))) hxL
    rw [inv_mul_cancel_left] at this
    exact h.t_not_mem_L this

end Light

section Torus

variable {K : Type} [Field K]
  [Finite K]

omit [Finite G] [Finite K] in
theorem J_mul_comm (d : G2Data L K) {x y : G} (hx : x ∈ d.J) (hy : y ∈ d.J) :
    x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := d.mem_image.1 hx
  obtain ⟨b, hb, rfl⟩ := d.mem_image.1 hy
  rw [← map_mul, ← map_mul]
  exact congrArg d.emb (Subtype.ext (Model.J_comm ha hb))

omit [Finite G] in
theorem odd_card_J₂ (d : G2Data L K) (hK : Nat.card K = 2 ^ f) : Odd (Nat.card d.J₂) := by
  rw [show d.J₂ = d.Ji 1 from rfl, (d.yamada_3_9_1_G 1).2, hK]
  have h1 : 1 < 2 ^ f := hK ▸ Finite.one_lt_card
  obtain ⟨k, hk⟩ := dvd_pow_self 2 (show f ≠ 0 by rintro rfl; simp at h1)
  rw [hk] at h1 ⊢
  exact ⟨k - 1, by omega⟩

theorem exists_centralizer_J₂_mul (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {M N : Subgroup G} (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set G))
    (hJM : d.J₂ ≤ normalizer (M : Set G)) (hJN : d.J₂ ≤ normalizer (N : Set G))
    (hM : IsPGroup 2 M) {m : G} (hm : m ∈ M) (hfix : ∀ j ∈ d.J₂, m⁻¹ * (j * m * j⁻¹) ∈ N) :
    ∃ c ∈ M ⊓ centralizer (d.J₂ : Set G), ∃ n ∈ N, m = c * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent M := hM.isNilpotent
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hM
  refine Common.exists_mem_inf_centralizer_mul_of_coprime hNM hMN hJM hJN inferInstance ?_ hm
    hfix
  rw [hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 (odd_card_J₂ d hK))

end Torus

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [CharP K 2] in
theorem S_inf_centralizer_Ji_of_four_le (d : G2Data L K) (h4 : 4 ≤ Nat.card K) (i : Fin 6)
    (hi : 8 ≤ Nat.card K ∨ i ∉ ({0, 3, 4} : Finset (Fin 6))) :
    d.S ⊓ centralizer (d.Ji i : Set G) = d.rootGroup (Model.yamadaRoot i) := by
  rw [G2Data.S, G2Data.Ji, ← d.image_inf_centralizer _ (G2Data.Ji_le_adjointGroup (K := K) i),
    Model.S_inf_centralizer_Ji h4 i hi]
  rfl

theorem J₂_facts (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.J₂ ≤ d.J ∧ d.J₂ ≤ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ∧
      d.S ⊓ centralizer (d.J₂ : Set G) = d.rootGroup g2v ∧
      d.J₂ ≤ normalizer (d.rootGroup g2u : Set G) ∧
      (∀ x ∈ d.rootGroup g2u, x ≠ 1 → ∀ y ∈ d.rootGroup g2u, y ≠ 1 →
        ∃ j ∈ d.J₂, j * x * j⁻¹ = y) ∧
      ∀ x ∈ d.rootGroup g2u, x ≠ 1 → ∀ j ∈ d.J₂, j * x = x * j → j = 1 := by
  have hJ₂J : d.J₂ ≤ d.J := d.image_mono inf_le_left
  have hJ₆J : d.Ji 5 ≤ d.J := d.image_mono inf_le_left
  have hJN : d.J ≤ L ⊓ normalizer (d.S : Set G) := by
    rw [d.yamada_3_13_1_G.2.2]
    exact le_sup_left
  have hJC : d.J ≤ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) := fun j hj =>
    Subgroup.mem_inf.2 ⟨h.L_le_centralizer (Subgroup.mem_inf.1 (hJN hj)).1,
      (Subgroup.mem_inf.1 (hJN hj)).2⟩
  have hC := fun i (hi : i ∉ ({0, 3, 4} : Finset (Fin 6))) =>
    S_inf_centralizer_Ji_of_four_le d (hK ▸ h.four_le) i (Or.inr hi)
  have h92 := d.yamada_3_9_2_G (i := 1) (k := 5) (by decide)
  obtain ⟨hbot, htr⟩ := h92.2 (Or.inr (by decide))
  refine ⟨hJ₂J, hJ₂J.trans hJC, hC 1 (by decide), fun j hj => ?_, fun x hx hx1 y hy hy1 =>
    htr x hx hx1 y hy hy1, fun x hx hx1 j hj hjx => ?_⟩
  · rw [show d.rootGroup g2u = d.S ⊓ centralizer (d.Ji 5 : Set G) from (hC 5 (by decide)).symm]
    refine Common.mem_normalizer_inf (Subgroup.mem_inf.1 (hJN (hJ₂J hj))).2
      (Subgroup.le_normalizer (mem_centralizer_iff.2 fun y hy => ?_))
    exact J_mul_comm d (hJ₆J hy) (hJ₂J hj)
  · have hj' : j ∈ d.Ji 1 ⊓ centralizer {x} :=
      Subgroup.mem_inf.2 ⟨hj, mem_centralizer_singleton_iff.2 hjx⟩
    rw [h92.1 x hx hx1, hbot] at hj'
    exact (Subgroup.mem_bot).1 hj'

theorem J₂_conj_W (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {j w : G} (hj : j ∈ d.J₂) (hw : w ∈ d.W) :
    j * w * j⁻¹ ∈ d.W ∧ w⁻¹ * (j * w * j⁻¹) ∈ d.Y := by
  obtain ⟨-, hJC, hC, -⟩ := h.J₂_facts d hK
  obtain ⟨-, -, hYW, -⟩ := d.inclusions
  have hWdef := d.yamada_defs.2.2.1
  have hjY : j ∈ normalizer (d.Y : Set G) :=
    (h.centralizer_inf_normalizer_S_le d hK hD).2.2 (hJC hj)
  have hAS : d.rootGroup g2v ≤ d.S := hC.ge.trans inf_le_left
  have hAW : d.rootGroup g2v ≤ d.W := le_sup_left.trans hWdef.le
  rw [← hWdef] at hw
  obtain ⟨a, ha, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer' (hAS.trans d.S_le_normalizers.2.1) _ hw
  have hja : j * a = a * j := mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hC.ge ha)).2 j hj
  have hjy : j * y * j⁻¹ ∈ d.Y := (mem_normalizer_iff.1 hjY _).1 hy
  have e1 : j * (a * y) * j⁻¹ = a * (j * y * j⁻¹) := by
    calc j * (a * y) * j⁻¹ = j * a * y * j⁻¹ := by group
      _ = a * (j * y * j⁻¹) := by rw [hja]; group
  rw [e1, show (a * y)⁻¹ * (a * (j * y * j⁻¹)) = y⁻¹ * (j * y * j⁻¹) by group]
  exact ⟨mul_mem (hAW ha) (hYW hjy), mul_mem (inv_mem hy) hjy⟩

theorem rootGroup_u_sup_yamadaV₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    d.rootGroup g2u ⊔ yamadaV₂ d t = yamadaE₂ d t ∧ d.rootGroup g2u ⊓ yamadaV₂ d t = ⊥ ∧
      d.rootGroup g2u ≤ normalizer (yamadaV₂ d t : Set G) := by
  obtain ⟨-, -, hYW, hXF, hWF, hFD, -, hDS, -⟩ := d.inclusions
  obtain ⟨-, hX, -, hF, -, -, hXW, -⟩ := d.yamada_defs
  have hAX : d.rootGroup g2u ≤ d.X := le_sup_left.trans hX.le
  have hAS : d.rootGroup g2u ≤ d.S := hAX.trans (hXF.trans (hFD.trans hDS))
  have hSV : d.S ≤ normalizer (yamadaV₂ d t : Set G) := fun s hs =>
    (h.normalizer_tY_le d hK hD).2.2
      ((h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).2
        (mem_sup_left (mem_sup_right hs)))
  have hAE : d.rootGroup g2u ≤ yamadaE₂ d t :=
    (hAX.trans hXF).trans (le_sup_left.trans le_sup_left)
  have hVE : yamadaV₂ d t ≤ yamadaE₂ d t := sup_le_sup_right (sup_le_sup_right hWF _) _
  have hWV : d.W ≤ yamadaV₂ d t := le_sup_left.trans le_sup_left
  have hFAV : d.F ≤ d.rootGroup g2u ⊔ yamadaV₂ d t := by
    rw [← hF, ← hX]
    exact sup_le (sup_le le_sup_left ((hYW.trans hWV).trans le_sup_right))
      (hWV.trans le_sup_right)
  have hAc : Nat.card (d.rootGroup g2u) = Nat.card K :=
    (d.card_image (rootSubgroup_le_adjointGroup (K := K) (τ := .G2) g2u)).trans
      (card_rootSubgroup (τ := .G2) (K := K) g2u)
  have hAY : d.Y ⊓ d.rootGroup g2u = ⊥ := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := d.Y) (B := d.rootGroup g2u)
      (hAS.trans d.S_le_normalizers.2.1)
    rw [sup_comm, hX, d.cards.2.2.1, d.cards.2.1, hAc] at h1
    have hq : 0 < Nat.card K ^ 3 := by
      have : 0 < Nat.card K := Nat.card_pos
      positivity
    refine Subgroup.card_eq_one.1 (Nat.eq_of_mul_eq_mul_left hq ?_)
    rw [h1]
    ring
  have hAW : d.rootGroup g2u ⊓ d.W = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxA, hxW⟩ := Subgroup.mem_inf.1 hx
    rw [← hAY]
    refine Subgroup.mem_inf.2 ⟨?_, hxA⟩
    rw [← hXW]
    exact Subgroup.mem_inf.2 ⟨hAX hxA, hxW⟩
  have hAV : d.rootGroup g2u ⊓ yamadaV₂ d t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxA, hxV⟩ := Subgroup.mem_inf.1 hx
    have hxL : x ∈ L := d.image_le _ hxA
    have hW₂L : yamadaW₂ d t ⊓ centralizer ({t} : Set G) ≤ L := by
      rw [h.yamadaW₂_inf_centralizer d hK hD]
      exact d.image_le _
    have hxW₂ := h.mem_of_mem_sup_zpowers_of_le (h.t_mem_normalizer_yamadaW₂ d hK hD).1 hW₂L hxL hxV
    have hxW : x ∈ d.W := by
      rw [← h.yamadaW₂_inf_centralizer d hK hD]
      exact Subgroup.mem_inf.2 ⟨hxW₂, h.L_le_centralizer hxL⟩
    rw [← hAW]
    exact Subgroup.mem_inf.2 ⟨hxA, hxW⟩
  refine ⟨le_antisymm (sup_le hAE hVE) (sup_le (sup_le hFAV ?_) ?_), hAV, hAS.trans hSV⟩
  · exact (le_sup_right.trans le_sup_left).trans le_sup_right
  · exact (le_sup_right : zpowers t ≤ yamadaV₂ d t).trans le_sup_right

theorem M_inf_yamadaC₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.M ⊓ yamadaC₂ d t = d.F := by
  obtain ⟨-, -, -, -, -, hFD, hFM, -⟩ := d.inclusions
  refine le_antisymm (fun x hx => ?_) (le_inf hFM ((hFD.trans le_sup_left).trans le_sup_left))
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.1 hx
  rw [← d.yamada_defs.2.2.2.2.2.2.2.1]
  exact Subgroup.mem_inf.2 ⟨h.mem_D_of_mem_yamadaC₂ d hK hD hxC (d.image_le _ hxM), hxM⟩

theorem centralizer_inf_normalizer_S_le_normalizers (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (yamadaV₂ d t : Set G) ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
        normalizer (yamadaL₃ d t : Set G) ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
        normalizer (yamadaE₃ d t : Set G) ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
        normalizer (yamadaE₂ d t : Set G) := by
  have hV : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaV₂ d t : Set G) := fun x hx =>
    (h.normalizer_tY_le d hK hD).2.2
      ((h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).2 (mem_sup_right hx))
  have hL₃ : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaL₃ d t : Set G) := hV.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hCs : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaCstar d t : Set G) :=
    (h.centralizer_inf_normalizer_S_le d hK hD).1.trans
      (LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hR₂ := (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).1
  refine ⟨hV, hL₃, fun x hx => Common.mem_normalizer_inf (hL₃ hx) (Common.mem_normalizer_inf
    (mem_normalizer_sup (hL₃ hx) (Subgroup.mem_inf.1 hx).2) (hCs hx)), fun x hx => ?_⟩
  rw [← h.yamadaL₂_inf_yamadaC₂ d hK hD, (h.yamadaR₃_facts hW d hK hD).2.2.2.2]
  exact Common.mem_normalizer_inf (hV.trans (h.normalizer_le_normalizer_yamadaL₂ hW d hK hD) hx)
    (Common.mem_normalizer_inf (hCs hx) (hR₂ hx))

theorem yamadaE₃_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaE₂ d t ≤ yamadaE₃ d t ∧ yamadaE₃ d t ⊓ d.S = d.F ∧
      yamadaR₃ d t ≤ normalizer (yamadaE₂ d t : Set G) ∧
      yamadaR₃ d t ≤ normalizer (yamadaE₃ d t : Set G) ∧
      yamadaL₃ d t ⊓ yamadaC₂ d t ≤ yamadaE₂ d t ∧
      Nat.card (yamadaE₃ d t) = 2 * Nat.card K ^ 7 ∧ d.S ⊔ yamadaE₃ d t = yamadaR₃ d t := by
  obtain ⟨hL₂L₃, -, hR₃L₃, hR₃V₂, hL₃S⟩ := h.yamadaL₃_facts hW d hK hD
  obtain ⟨-, hR₂R₃, -, -, hC₂⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨hR₃C₂, hR₃eq, hC₃R₂, hR₃C₃, -⟩ := h.yamada_5_30_1_R₃ hW d hK hD
  obtain ⟨-, -, -, -, -, hFD, -, hDS, hMS, -⟩ := d.inclusions
  have hL₂C₂ := h.yamadaL₂_inf_yamadaC₂ d hK hD
  have hMC₂ := h.M_inf_yamadaC₂ d hK hD
  have hC₂C₃ : yamadaC₂ d t ≤ yamadaC₃ d t := hC₃R₂.ge.trans inf_le_left
  have hE₂E₃ : yamadaE₂ d t ≤ yamadaE₃ d t :=
    le_inf ((hL₂C₂.ge.trans inf_le_left).trans hL₂L₃) ((hL₂C₂.ge.trans inf_le_right).trans hC₂C₃)
  have hR₃E₂ : yamadaR₃ d t ≤ normalizer (yamadaE₂ d t : Set G) := fun x hx => by
    rw [← hL₂C₂]
    exact Common.mem_normalizer_inf (h.normalizer_le_normalizer_yamadaL₂ hW d hK hD (hR₃V₂ hx))
      (hR₃C₂ hx)
  have hR₃E₃ : yamadaR₃ d t ≤ normalizer (yamadaE₃ d t : Set G) := fun x hx =>
    Common.mem_normalizer_inf (hR₃L₃ hx) (hR₃C₃ hx)
  have hML₂ : d.M ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d hK)
  have hE₃S : yamadaE₃ d t ⊓ d.S = d.F := by
    refine le_antisymm (fun x hx => ?_)
      (le_inf ((le_sup_left.trans le_sup_left).trans hE₂E₃) (hFD.trans hDS))
    obtain ⟨hxE, hxS⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxL₃, hxC₃⟩ := Subgroup.mem_inf.1 hxE
    have hxM : x ∈ d.M := hL₃S.le (Subgroup.mem_inf.2 ⟨hxL₃, hxS⟩)
    have hxC₂ : x ∈ yamadaC₂ d t := hC₂.ge (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxC₃).2,
      (le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t) (hML₂ hxM)⟩)
    exact hMC₂.le (Subgroup.mem_inf.2 ⟨hxM, hxC₂⟩)
  have hL₃C₂ : yamadaL₃ d t ⊓ yamadaC₂ d t ≤ yamadaE₂ d t := fun x hx => by
    obtain ⟨hxL₃, hxC₂⟩ := Subgroup.mem_inf.1 hx
    have hxR₂ : x ∈ yamadaR₂ d t := (hC₂.le.trans inf_le_right) hxC₂
    obtain ⟨l, hl, s, hs, rfl⟩ :=
      Common.exists_mul_of_le_normalizer (h.S_le_normalizer_yamadaL₂ d) _ hxR₂
    have hsM : s ∈ d.M := by
      rw [← hL₃S]
      refine Subgroup.mem_inf.2 ⟨?_, hs⟩
      have := mul_mem (inv_mem (hL₂L₃ hl)) hxL₃
      rwa [inv_mul_cancel_left] at this
    rw [← hL₂C₂]
    exact Subgroup.mem_inf.2 ⟨mul_mem hl (hML₂ hsM), hxC₂⟩
  have hR₃c := h.card_yamadaL₃_R₃ hW d hK hD
  have hq : 0 < Nat.card K := Nat.card_pos
  have hC₃c : Nat.card (yamadaC₃ d t) = 2 * Nat.card K ^ 8 := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaC₃ d t) (B := yamadaR₂ d t)
      (hR₂R₃.trans hR₃C₃)
    rw [← hR₃eq, hC₃R₂, hR₃c.2, (h.card_yamadaC₂_E₂_V₂ d hK hD).1, h.card_yamadaR₂ d hK] at h1
    refine Nat.eq_of_mul_eq_mul_right (show 0 < 2 * Nat.card K ^ 8 by positivity) ?_
    rw [← h1]
    ring
  have hlow : 2 * Nat.card K ^ 7 ≤ Nat.card (yamadaE₃ d t) := by
    have h1 : Nat.card (yamadaL₃ d t ⊔ yamadaC₃ d t : Subgroup G) * Nat.card (yamadaE₃ d t) =
        Nat.card (yamadaL₃ d t) * Nat.card (yamadaC₃ d t) :=
      Common.card_sup_mul_card_inf_eq ((inf_le_left : yamadaC₃ d t ≤ yamadaR₃ d t).trans hR₃L₃)
    have h2 : Nat.card (yamadaL₃ d t ⊔ yamadaC₃ d t : Subgroup G) ≤ 2 * Nat.card K ^ 9 := by
      rw [← hR₃c.2]
      exact Subgroup.card_le_of_le (sup_le le_sup_left inf_le_left)
    rw [hR₃c.1, hC₃c] at h1
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 2 * Nat.card K ^ 9 by positivity)
    calc 2 * Nat.card K ^ 7 * (2 * Nat.card K ^ 9) =
          Nat.card (yamadaL₃ d t ⊔ yamadaC₃ d t : Subgroup G) * Nat.card (yamadaE₃ d t) := by
          rw [h1]
          ring
      _ ≤ 2 * Nat.card K ^ 9 * Nat.card (yamadaE₃ d t) := Nat.mul_le_mul_right _ h2
      _ = Nat.card (yamadaE₃ d t) * (2 * Nat.card K ^ 9) := by ring
  have hE₃R₃ : yamadaE₃ d t ≤ yamadaR₃ d t := inf_le_left.trans le_sup_left
  have h3 : Nat.card (yamadaE₃ d t ⊔ d.S : Subgroup G) * Nat.card K ^ 4 =
      Nat.card (yamadaE₃ d t) * Nat.card K ^ 6 := by
    have := Common.card_sup_mul_card_inf_eq (A := yamadaE₃ d t) (B := d.S)
      ((le_sup_right : d.S ≤ yamadaR₃ d t).trans hR₃E₃)
    rwa [hE₃S, d.cards.2.2.2.2.1, d.cards.2.2.2.2.2.2.2] at this
  have hle : yamadaE₃ d t ⊔ d.S ≤ yamadaR₃ d t := sup_le hE₃R₃ le_sup_right
  have hcard : Nat.card (yamadaE₃ d t) = 2 * Nat.card K ^ 7 := by
    refine le_antisymm (Nat.le_of_mul_le_mul_right (c := Nat.card K ^ 6) ?_ (by positivity))
      hlow
    calc Nat.card (yamadaE₃ d t) * Nat.card K ^ 6 =
          Nat.card (yamadaE₃ d t ⊔ d.S : Subgroup G) * Nat.card K ^ 4 := h3.symm
      _ ≤ Nat.card (yamadaR₃ d t) * Nat.card K ^ 4 :=
          Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hle)
      _ = 2 * Nat.card K ^ 7 * Nat.card K ^ 6 := by rw [hR₃c.2]; ring
  refine ⟨hE₂E₃, hE₃S, hR₃E₂, hR₃E₃, hL₃C₂, hcard, ?_⟩
  rw [sup_comm]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h5 : Nat.card (yamadaE₃ d t ⊔ d.S : Subgroup G) * Nat.card K ^ 4 =
      Nat.card (yamadaR₃ d t) * Nat.card K ^ 4 := by
    rw [h3, hcard, hR₃c.2]
    ring
  exact (Nat.eq_of_mul_eq_mul_right (by positivity) h5).ge

theorem inv_mul_conj_mem_yamadaE₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {e j : G}
    (he : e ∈ yamadaE₃ d t) (hj : j ∈ d.J₂) : e⁻¹ * (j * e * j⁻¹) ∈ yamadaE₂ d t := by
  obtain ⟨-, hJC, -⟩ := h.J₂_facts d hK
  obtain ⟨-, hJL₃, hJE₃, -⟩ := h.centralizer_inf_normalizer_S_le_normalizers hW d hK hD
  obtain ⟨_, _, φ, hφ, -⟩ := h.yamada_5_23_3 hW d hK hD
  have heL₃ : e ∈ yamadaL₃ d t := (Subgroup.mem_inf.1 he).1
  obtain ⟨w, hw, hew⟩ := (h.yamada_5_23_2 hW d hK hD).1 e heL₃
  have hjC := hJC hj
  have hjt : j * t = t * j := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hjC).1
  have hjeL₃ : j * e * j⁻¹ ∈ yamadaL₃ d t := (mem_normalizer_iff.1 (hJL₃ hjC) _).1 heL₃
  obtain ⟨hjw, hwY⟩ := h.J₂_conj_W d hK hD hj hw
  have hcalc : (j * e * j⁻¹) * t * (j * e * j⁻¹)⁻¹ = t * (j * w * j⁻¹) := by
    have hjt' : j⁻¹ * t * j = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
    calc (j * e * j⁻¹) * t * (j * e * j⁻¹)⁻¹ = j * (e * (j⁻¹ * t * j) * e⁻¹) * j⁻¹ := by group
      _ = j * (t * w) * j⁻¹ := by rw [hjt', hew]
      _ = j * t * w * j⁻¹ := by group
      _ = t * (j * w * j⁻¹) := by rw [hjt]; group
  have h1 := hφ ⟨e, heL₃⟩ ⟨w, hw⟩ hew
  have h2 := hφ ⟨j * e * j⁻¹, hjeL₃⟩ ⟨j * w * j⁻¹, hjw⟩ hcalc
  have h3 : (QuotientGroup.mk ⟨w, hw⟩ : d.W ⧸ d.Y.subgroupOf d.W) =
      QuotientGroup.mk ⟨j * w * j⁻¹, hjw⟩ := by
    rw [QuotientGroup.eq, mem_subgroupOf]
    exact hwY
  have h4 := φ.injective (h1.trans (h3.trans h2.symm))
  rw [QuotientGroup.eq, mem_subgroupOf] at h4
  have h5 : e⁻¹ * (j * e * j⁻¹) ∈ yamadaL₂ d t := h4
  have h6 : e⁻¹ * (j * e * j⁻¹) ∈ yamadaE₃ d t :=
    mul_mem (inv_mem he) ((mem_normalizer_iff.1 (hJE₃ hjC) _).1 he)
  rw [← h.yamadaL₂_inf_yamadaC₂ d hK hD]
  refine Subgroup.mem_inf.2 ⟨h5, ?_⟩
  rw [(h.yamadaR₃_facts hW d hK hD).2.2.2.2]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 h6).2).2, mem_sup_left h5⟩

theorem yamadaR₃_inf_centralizer_J₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₃ d t ⊓ centralizer (d.J₂ : Set G) ≤ yamadaE₃ d t := fun c hc => by
  obtain ⟨hcR, hcJ⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨hJ₂J, hJC, hC, -⟩ := h.J₂_facts d hK
  obtain ⟨-, -, hJE₃, -⟩ := h.centralizer_inf_normalizer_S_le_normalizers hW d hK hD
  obtain ⟨-, hE₃S, -, hR₃E₃, -, -, hSE⟩ := h.yamadaE₃_facts hW d hK hD
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -⟩ := d.inclusions
  have hJF : d.J₂ ≤ normalizer (d.F : Set G) := fun j hj => by
    have : j ∈ L ⊓ normalizer (d.F : Set G) := by
      rw [d.yamada_3_13_1_G.2.1]
      exact mem_sup_left (hJ₂J hj)
    exact (Subgroup.mem_inf.1 this).2
  rw [← hSE] at hcR
  obtain ⟨s, hs, e, he, rfl⟩ := Common.exists_mul_of_le_normalizer'
    ((le_sup_right : d.S ≤ yamadaR₃ d t).trans hR₃E₃) _ hcR
  have hfix : ∀ j ∈ d.J₂, s⁻¹ * (j * s * j⁻¹) ∈ d.F := fun j hj => by
    have hjc : j * (s * e) = s * e * j := mem_centralizer_iff.1 hcJ j hj
    have hjS := (Subgroup.mem_inf.1 (hJC hj)).2
    rw [← hE₃S]
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (inv_mem hs) ((mem_normalizer_iff.1 hjS _).1 hs)⟩
    rw [show s⁻¹ * (j * s * j⁻¹) = e * (j * e * j⁻¹)⁻¹ by
      calc s⁻¹ * (j * s * j⁻¹) = s⁻¹ * (j * (s * e) * j⁻¹) * (j * e * j⁻¹)⁻¹ := by group
        _ = e * (j * e * j⁻¹)⁻¹ := by rw [hjc]; group]
    exact mul_mem he (inv_mem ((mem_normalizer_iff.1 (hJE₃ (hJC hj)) _).1 he))
  obtain ⟨c', hc', n, hn, rfl⟩ := exists_centralizer_J₂_mul d hK (hFD.trans hDS)
    d.S_le_normalizers.2.2.2.2.1 (fun j hj => (Subgroup.mem_inf.1 (hJC hj)).2) hJF
    d.isSylowOf_S.isPGroup hs hfix
  have hc'F : c' ∈ d.F := by
    rw [hC] at hc'
    exact hWF ((le_sup_left.trans d.yamada_defs.2.2.1.le) hc')
  have hFE₃ : d.F ≤ yamadaE₃ d t := hE₃S.ge.trans inf_le_left
  exact mul_mem (mul_mem (hFE₃ hc'F) (hFE₃ hn)) he

theorem yamadaE₂_inf_centralizer_J₂_le (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaE₂ d t ⊓ centralizer (d.J₂ : Set G) ≤ yamadaV₂ d t := fun x hx => by
  obtain ⟨hxE, hxJ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨-, hJC, -, hJA, -, hreg⟩ := h.J₂_facts d hK
  obtain ⟨hE, hAV, hAN⟩ := h.rootGroup_u_sup_yamadaV₂ d hK hD
  have hJV : d.J₂ ≤ normalizer (yamadaV₂ d t : Set G) := fun j hj =>
    (h.normalizer_tY_le d hK hD).2.2
      ((h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).2
        (mem_sup_right (hJC hj)))
  rw [← hE] at hxE
  obtain ⟨a, ha, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer' hAN _ hxE
  by_cases ha1 : a = 1
  · rw [ha1, one_mul]
    exact hv
  exfalso
  have hall : ∀ j ∈ d.J₂, j = 1 := fun j hj => by
    refine hreg a ha ha1 j hj ?_
    have hjx : j * (a * v) = a * v * j := mem_centralizer_iff.1 hxJ j hj
    have hmem : a⁻¹ * (j * a * j⁻¹) ∈ d.rootGroup g2u ⊓ yamadaV₂ d t := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) ((mem_normalizer_iff.1 (hJA hj) _).1 ha),
        ?_⟩
      rw [show a⁻¹ * (j * a * j⁻¹) = v * (j * v * j⁻¹)⁻¹ by
        calc a⁻¹ * (j * a * j⁻¹) = a⁻¹ * (j * (a * v) * j⁻¹) * (j * v * j⁻¹)⁻¹ := by group
          _ = v * (j * v * j⁻¹)⁻¹ := by rw [hjx]; group]
      exact mul_mem hv (inv_mem ((mem_normalizer_iff.1 (hJV hj) _).1 hv))
    rw [hAV, Subgroup.mem_bot] at hmem
    calc j * a = a * (a⁻¹ * (j * a * j⁻¹)) * j := by group
      _ = a * j := by rw [hmem, mul_one]
  have hbot : d.J₂ = ⊥ := eq_bot_iff.2 fun j hj => (Subgroup.mem_bot).2 (hall j hj)
  have hc := (d.yamada_3_9_1_G 1).2
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  rw [show d.Ji 1 = d.J₂ from rfl, hbot, Subgroup.card_bot] at hc
  omega

theorem yamada_5_30_1_E₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaE₃ d t ≤ normalizer (yamadaV₂ d t : Set G) ∧
      yamadaE₃ d t = yamadaV₃ d t ⊔ yamadaE₂ d t ∧ yamadaV₃ d t ⊓ yamadaE₂ d t = yamadaV₂ d t ∧
      yamadaE₃ d t ≤ normalizer (yamadaV₃ d t : Set G) ∧
      yamadaE₃ d t ≤ normalizer (yamadaE₂ d t : Set G) ∧
      (∀ x ∈ yamadaE₃ d t, x * x ∈ yamadaV₂ d t) ∧
      (∀ x ∈ yamadaE₃ d t, ∀ y ∈ yamadaE₃ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaV₂ d t) ∧
      Nat.card (yamadaE₃ d t) = Nat.card K ^ 2 * Nat.card (yamadaV₂ d t) := by
  obtain ⟨hJ₂J, hJC, -, hJA, htrans, hreg⟩ := h.J₂_facts d hK
  obtain ⟨hR₃R, -, -, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨-, -, -, hR₃V₂, -⟩ := h.yamadaL₃_facts hW d hK hD
  obtain ⟨-, -, -, -, -, hsqR₃, -, -⟩ := h.yamada_5_30_1_R₃ hW d hK hD
  obtain ⟨hE₂E₃, -, hR₃E₂, -, hL₃C₂, hcard, -⟩ := h.yamadaE₃_facts hW d hK hD
  obtain ⟨-, -, hJE₃, hJE₂⟩ := h.centralizer_inf_normalizer_S_le_normalizers hW d hK hD
  obtain ⟨hAE, hAV, hAN⟩ := h.rootGroup_u_sup_yamadaV₂ d hK hD
  have hR₃p : IsPGroup 2 (yamadaR₃ d t) := (h.isPGroup_yamadaRstar d).to_le hR₃R
  have hJV : d.J₂ ≤ normalizer (yamadaV₂ d t : Set G) := fun j hj =>
    (h.normalizer_tY_le d hK hD).2.2
      ((h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).2
        (mem_sup_right (hJC hj)))
  have hV₂E₂ : yamadaV₂ d t ≤ yamadaE₂ d t := le_sup_right.trans hAE.le
  have hE₃R₃ : yamadaE₃ d t ≤ yamadaR₃ d t := inf_le_left.trans le_sup_left
  have hE₃V₂ : yamadaE₃ d t ≤ normalizer (yamadaV₂ d t : Set G) :=
    inf_le_left.trans (LieType.BorelTits.pCoreOf_le 2 _)
  have hE₂V₂ : yamadaE₂ d t ≤ normalizer (yamadaV₂ d t : Set G) := hE₂E₃.trans hE₃V₂
  have hCV₂ : yamadaR₃ d t ⊓ centralizer (d.J₂ : Set G) ≤ normalizer (yamadaV₂ d t : Set G) :=
    inf_le_left.trans hR₃V₂
  have hCJ := h.yamadaR₃_inf_centralizer_J₂_le hW d hK hD
  have hV₃E₃ : yamadaV₃ d t ≤ yamadaE₃ d t := sup_le hCJ (hV₂E₂.trans hE₂E₃)
  have hE₃eq : yamadaE₃ d t = yamadaV₃ d t ⊔ yamadaE₂ d t := by
    refine le_antisymm (fun e he => ?_) (sup_le hV₃E₃ hE₂E₃)
    obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_J₂_mul d hK hE₂E₃ (hE₃R₃.trans hR₃E₂)
      (fun j hj => hJE₃ (hJC hj)) (fun j hj => hJE₂ (hJC hj)) (hR₃p.to_le hE₃R₃) he
      (fun j hj => h.inv_mul_conj_mem_yamadaE₂ hW d hK hD he hj)
    exact mul_mem (mem_sup_left (mem_sup_left (Subgroup.mem_inf.2
      ⟨hE₃R₃ (Subgroup.mem_inf.1 hc).1, (Subgroup.mem_inf.1 hc).2⟩))) (mem_sup_right hn)
  have hV₃E₂ : yamadaV₃ d t ⊓ yamadaE₂ d t = yamadaV₂ d t := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hV₂E₂)
    obtain ⟨hxV, hxE⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨c, hc, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer' hCV₂ _ hxV
    have hcE : c ∈ yamadaE₂ d t := by
      have := mul_mem hxE (inv_mem (hV₂E₂ hv))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (h.yamadaE₂_inf_centralizer_J₂_le d hK hD
      (Subgroup.mem_inf.2 ⟨hcE, (Subgroup.mem_inf.1 hc).2⟩)) hv
  have hE9 : ∀ c ∈ yamadaR₃ d t ⊓ centralizer (d.J₂ : Set G), ∀ e ∈ yamadaE₂ d t,
      c * e * c⁻¹ * e⁻¹ ∈ yamadaV₂ d t := fun c hc => by
    obtain ⟨hcR, hcJ⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨m, hm⟩ := hR₃p ⟨c, hcR⟩
    have hcm : c ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    exact conj_mul_inv_mem_of_regular (le_sup_left.trans hAE.le)
      (fun e he => Common.exists_mul_of_le_normalizer' hAN e (hAE.ge he)) hE₂V₂ hAV hJA hJV
      (fun j hj k hk => J_mul_comm d (hJ₂J hj) (hJ₂J hk)) (odd_card_J₂ d hK) htrans hreg
      (hR₃E₂ hcR) (hR₃V₂ hcR) hcJ hcm
  have hE₂NV₃ : yamadaE₂ d t ≤ normalizer (yamadaV₃ d t : Set G) := fun e he =>
    mem_normalizer_of_conj_mem fun x hx => by
      obtain ⟨c, hc, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer' hCV₂ _ hx
      rw [show e * (c * v) * e⁻¹ = c * (c⁻¹ * e * c⁻¹⁻¹ * e⁻¹) * (e * v * e⁻¹) by group]
      exact mul_mem (mul_mem (mem_sup_left hc) (mem_sup_right (hE9 _ (inv_mem hc) e he)))
        (mem_sup_right ((mem_normalizer_iff.1 (hE₂V₂ he) _).1 hv))
  have hE₃NV₃ : yamadaE₃ d t ≤ normalizer (yamadaV₃ d t : Set G) :=
    hE₃eq.le.trans (sup_le Subgroup.le_normalizer hE₂NV₃)
  have hE₃NE₂ : yamadaE₃ d t ≤ normalizer (yamadaE₂ d t : Set G) := hE₃R₃.trans hR₃E₂
  have hsqC : ∀ c ∈ yamadaR₃ d t ⊓ centralizer (d.J₂ : Set G), c * c ∈ yamadaV₂ d t :=
    fun c hc => by
      have hcL₃ := (Subgroup.mem_inf.1 (hCJ hc)).1
      exact h.yamadaE₂_inf_centralizer_J₂_le d hK hD (Subgroup.mem_inf.2
        ⟨hL₃C₂ (Subgroup.mem_inf.2 ⟨mul_mem hcL₃ hcL₃, hsqR₃ c (Subgroup.mem_inf.1 hc).1⟩),
          mul_mem (Subgroup.mem_inf.1 hc).2 (Subgroup.mem_inf.1 hc).2⟩)
  obtain ⟨hsqV₃, -⟩ := mul_self_mem_of_sup (N := yamadaV₂ d t) hCV₂
    (sup_le hCV₂ Subgroup.le_normalizer) hsqC (fun b hb => mul_mem hb hb)
    (fun a ha b hb => mul_mem ((mem_normalizer_iff.1 (hCV₂ ha) _).1 hb) (inv_mem hb))
  have hAX : d.rootGroup g2u ≤ d.X := le_sup_left.trans d.yamada_defs.2.1.le
  obtain ⟨hsqE₂, -⟩ := mul_self_mem_of_sup (N := yamadaV₂ d t) hAN (hAE.le.trans hE₂V₂)
    (fun a ha => by rw [X_mul_self d (hAX ha)]; exact one_mem _) (fun b hb => mul_mem hb hb)
    (fun a ha b hb => mul_mem ((mem_normalizer_iff.1 (hAN ha) _).1 hb) (inv_mem hb))
  obtain ⟨hsq, hcomm⟩ := mul_self_mem_of_sup (A := yamadaV₃ d t) (B := yamadaE₂ d t)
    (N := yamadaV₂ d t) (hV₃E₃.trans hE₃NE₂) (hE₃eq.ge.trans hE₃V₂) hsqV₃
    (fun e he => hsqE₂ e (hAE.ge he)) (fun x hx e he => by
      rw [← hV₃E₂]
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem ((mem_normalizer_iff.1
        ((hV₃E₃.trans hE₃NE₂) hx) _).1 he) (inv_mem he)⟩
      rw [show x * e * x⁻¹ * e⁻¹ = x * (e * x⁻¹ * e⁻¹) by group]
      exact mul_mem hx ((mem_normalizer_iff.1 (hE₂NV₃ he) _).1 (inv_mem hx)))
  refine ⟨hE₃V₂, hE₃eq, hV₃E₂, hE₃NV₃, hE₃NE₂, fun x hx => hsq x (hE₃eq.le hx),
    fun x hx y hy => hcomm x (hE₃eq.le hx) y (hE₃eq.le hy), ?_⟩
  rw [hcard, (h.card_yamadaC₂_E₂_V₂ d hK hD).2.2]
  ring

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
