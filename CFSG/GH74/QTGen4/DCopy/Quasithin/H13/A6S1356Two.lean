module

public import CFSG.Quasithin.H13.A6S1356Two
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1356
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_normalizer_V_of_TI_F4 (h1222 : Stmt12_2_2_F4) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) {W : Subgroup G} (hWV : W ≤ V) (hW : W ≠ ⊥)
    (hmW : ∀ w ∈ W, m * w * m⁻¹ ∈ V) : m ∈ Subgroup.normalizer (V : Set G) := by
  rcases h1222 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow with h | h
  · exact absurd h S.not_alt12_2_2
  have hTI := ((h L S.maximal S.h13.faithful S.fsu.quasisimple).2.2 V S.irr).2.1 m hm
  have hmem : ∀ x, x ∈ CFSG.conjugate V m ↔ m * x * m⁻¹ ∈ V := by
    intro x
    unfold CFSG.conjugate
    rw [Subgroup.mem_map_equiv]
    simp
  rcases hTI with h1 | h1
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← hmem, h1]
  · exfalso
    apply hW
    rw [eq_bot_iff, ← h1]
    exact fun w hw => ⟨hWV hw, (hmem w).2 (hmW w hw)⟩

theorem not_nondegenerate_F4
    (h1222 : Stmt12_2_2_F4) (hA : autOn T V ≤ autOn L V) (g : G)
    (hW : conjSub g S.V2 ≤ V) {a b : G} (ha : a ∈ conjSub g S.V2) (hb : b ∈ conjSub g S.V2) :
    dot (S.frame.ψ ⟨a, hW ha⟩ : P6) (S.frame.ψ ⟨b, hW hb⟩ : P6) ≠ 1 := by
  intro hdot
  set W := conjSub g S.V2 with hWdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQC : Q ≤ Subgroup.centralizer (W : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hW)
  have hQ2 : IsPGroup 2 Q := S.h13.sylow.1.to_le inf_le_left

  set P := conjSub g (T ⊓ Subgroup.centralizer (S.V2 : Set G)) with hPdef
  have hPC : P ≤ Subgroup.centralizer (W : Set G) := by
    rw [hWdef, conjSub_centralizer]
    exact conjSub_mono g inf_le_right
  have hP2 : IsPGroup 2 P := F7.isPGroup_conjSub (S.h13.sylow.1.to_le inf_le_left)
  have hQP : Nat.card Q < Nat.card P := by
    rw [hPdef, A5.card_conjSub']
    exact S.card_CTV_lt

  obtain ⟨S', hS', hQS'⟩ := A4.exists_isSylowTwoOf_ge hQC hQ2
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hS' hPC hP2
  have hPS' : Nat.card P ≤ Nat.card S' :=
    (Subgroup.card_le_of_le hx).trans (A5.card_conjSub' x S').le
  have hlt : Q < S' := lt_of_le_of_ne hQS' fun h => by
    rw [h] at hQP
    omega
  obtain ⟨s, hsS', hsQ, hsN⟩ := A5.exists_mem_normalizer_not_mem hS'.2.1 hlt
  have hsM : s ∈ Subgroup.normalizer (L : Set G) := S.normalizer_CTV_le hsN
  have hsC : s ∈ Subgroup.centralizer (W : Set G) := hS'.1 hsS'
  have hWne : W ≠ ⊥ := by
    rw [hWdef, Ne, conjSub_eq_bot_iff]
    intro h
    have := S.card_V2
    rw [h, Subgroup.card_bot] at this
    omega
  have hsV : s ∈ Subgroup.normalizer (V : Set G) :=
    S.mem_normalizer_V_of_TI_F4 h1222 hsM hW hWne fun w hw => by
      have := Subgroup.mem_centralizer_iff.mp hsC w hw
      rw [← this, mul_inv_cancel_right]
      exact hW hw

  have hfix : ∀ c (hc : c ∈ W), act4f (S.frame.ρ ⟨s, hsV⟩) (S.frame.ψ ⟨c, hW hc⟩ : P6) =
      (S.frame.ψ ⟨c, hW hc⟩ : P6) := by
    intro c hc
    have h := (S.conj_eq_iff ⟨s, hsV⟩ ⟨c, hW hc⟩).1 (by
      have := Subgroup.mem_centralizer_iff.mp hsC c hc
      calc s * c * s⁻¹ = c * s * s⁻¹ := by rw [this]
        _ = c := by group)
    exact congrArg Subtype.val h
  have h4 : (S.frame.ρ ⟨s, hsV⟩) ^ 4 = 1 := by
    obtain ⟨k, hk⟩ := hS'.2.1 ⟨s, hsS'⟩
    refine pow_four_of_pow_two_pow (k := k) ?_
    rw [← map_pow]
    have : (⟨s, hsV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hρ : S.frame.ρ ⟨s, hsV⟩ = 1 :=
    nondegFix _ _ (S.frame.ψ _).2 (S.frame.ψ _).2 hdot _ (hfix a ha) (hfix b hb) h4
      (S.sign_rho_eq_one hA _)
  have hsCV := (S.rho_eq_one_iff _).1 hρ

  have heq := F1.eq_of_isSylowTwoOf_le S.isSylowTwoOf_CTV inf_le_right
    (hS'.2.1.to_le inf_le_left) (le_inf hQS' inf_le_right)
  have hmem : s ∈ S' ⊓ Subgroup.centralizer (V : Set G) := ⟨hsS', hsCV⟩
  rw [← heq] at hmem
  exact hsQ hmem

theorem lemma13_5_6_two_of_A6_F4
    (h1222 : Stmt12_2_2_F4) (hA : autOn T V ≤ autOn L V) (g : G)
    (hW : conjSub g S.V2 ≤ V) : ∃ l ∈ L, conjSub g S.V2 = conjSub l S.V2 := by
  classical
  set W := conjSub g S.V2 with hWdef
  have hcardW : Nat.card W = 4 := by rw [hWdef, A5.card_conjSub', S.card_V2]

  obtain ⟨a, haW, ha1⟩ : ∃ a ∈ W, a ≠ 1 := by
    by_contra h
    push Not at h
    have : W = ⊥ := (Subgroup.eq_bot_iff_forall W).2 h
    rw [this, Subgroup.card_bot] at hcardW
    omega
  obtain ⟨b, hbW, hb1, hba⟩ : ∃ b ∈ W, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (W : Set G) ⊆ {1, a} := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    have : Nat.card W ≤ 2 := by
      calc Nat.card W = Nat.card (W : Set G) := rfl
        _ ≤ Nat.card ({1, a} : Set G) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by simp)
    omega
  have hinj : ∀ (u v : ↥V), (S.frame.ψ u : P6) = (S.frame.ψ v : P6) → (u : G) = v := by
    intro u v h
    exact congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
  have hα1 : (S.frame.ψ ⟨a, hW haW⟩ : P6) ≠ 1 := fun h => ha1 (by
    have := hinj ⟨a, hW haW⟩ 1 (by rw [map_one]; exact h)
    simpa using this)
  have hβ1 : (S.frame.ψ ⟨b, hW hbW⟩ : P6) ≠ 1 := fun h => hb1 (by
    have := hinj ⟨b, hW hbW⟩ 1 (by rw [map_one]; exact h)
    simpa using this)
  have hαβ : (S.frame.ψ ⟨a, hW haW⟩ : P6) ≠ (S.frame.ψ ⟨b, hW hbW⟩ : P6) := fun h =>
    hba (hinj _ _ h).symm
  rcases zmod2_cases (dot (S.frame.ψ ⟨a, hW haW⟩ : P6) (S.frame.ψ ⟨b, hW hbW⟩ : P6)) with hd | hd
  ·
    obtain ⟨σ, hσW, hσs⟩ := isoWit _ _ ⟨(S.frame.ψ _).2, (S.frame.ψ _).2, hα1, hβ1, hαβ⟩ hd
    obtain ⟨l, hlL, hl⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hσs)
    refine ⟨l, hlL, (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm⟩
    · intro x hx
      rw [mem_conjSub] at hx
      obtain ⟨hyV, hyW2⟩ := S.mem_pre.1 hx
      have hxy : x = l * ((l : G)⁻¹ * x * l) * (l : G)⁻¹ := by group
      have hxV : x ∈ V := by
        rw [hxy]
        exact (Subgroup.mem_normalizer_iff.mp l.2 _).mp hyV
      have hψ : (S.frame.ψ ⟨x, hxV⟩ : P6) =
          act4f σ (S.frame.ψ ⟨(l : G)⁻¹ * x * l, hyV⟩ : P6) := by
        have h1 := S.psi_conj l ⟨(l : G)⁻¹ * x * l, hyV⟩
        rw [hl] at h1
        have e : (⟨x, hxV⟩ : ↥V) = ⟨l * ((l : G)⁻¹ * x * l) * (l : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp l.2 _).mp hyV⟩ := Subtype.ext hxy
        rw [e, h1]
        rfl
      rcases hσW _ hyW2 with h | h | h | h <;> rw [← hψ] at h
      · have hx1 : x = ((1 : ↥V) : G) := hinj ⟨x, hxV⟩ 1 (by rw [map_one]; exact h)
        rw [hx1]
        exact W.one_mem
      · have hxa : x = a := hinj ⟨x, hxV⟩ ⟨a, hW haW⟩ h
        rw [hxa]
        exact haW
      · have hxb : x = b := hinj ⟨x, hxV⟩ ⟨b, hW hbW⟩ h
        rw [hxb]
        exact hbW
      · have hxab : x = a * b :=
          hinj ⟨x, hxV⟩ (⟨a, hW haW⟩ * ⟨b, hW hbW⟩) (by rw [map_mul]; exact h)
        rw [hxab]
        exact W.mul_mem haW hbW
    · rw [hcardW, A5.card_conjSub', S.card_V2]
  · exact absurd hd (S.not_nondegenerate_F4 h1222 hA g hW haW hbW)

end Setting4

@[expose] def Input1356TwoS6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ autOn T V ≤ autOn L V → ∀ g : G, conjSub g S.V2 ≤ V →
      ∃ l ∈ L, conjSub g S.V2 = conjSub l S.V2

theorem input1356Two_of_F4
    (h1222 : Stmt12_2_2_F4) (hS6 : Input1356TwoS6_F4) : Input1356Two_F4 := by
  intro G _ _ T L V S hNS g hW
  by_cases hA : autOn T V ≤ autOn L V
  · exact S.lemma13_5_6_two_of_A6_F4 h1222 hA g hW
  · exact hS6 G T L V S hNS hA g hW

end CFSG.Quasithin.H13.A6
