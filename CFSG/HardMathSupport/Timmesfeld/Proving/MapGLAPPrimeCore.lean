module

public import CFSG.HardMathSupport.Timmesfeld.Proving.CoatomStep
public import CFSG.HardMathSupport.Timmesfeld.Proving.ProvingFrattini

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {G : Type*} [Group G]

theorem map_GLAPPrimeCoreOf_centralizer_le_of_le [Finite G] {Z : Type*} [Group Z]
    (φ : G →* Z) {p : ℕ} (hp : p.Prime) :
    ∀ (n : ℕ) {B P : Subgroup G}, Nat.card P ≤ n → B ≤ P → IsPGroup p P → P ≤ B ⊔ φ.ker →
      (GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set G))).map φ ≤
        (GLAPPrimeCoreOf p (Subgroup.centralizer (P : Set G))).map φ := by
  intro n
  induction n with
  | zero =>
    intro B P hn _ _ _
    have := Nat.card_pos (α := P)
    omega
  | succ n ih =>
    intro B P hn hBP hP hPN
    rcases eq_or_lt_of_le hBP with rfl | hlt
    · exact le_rfl
    · have : Fact p.Prime := ⟨hp⟩
      have : Group.IsNilpotent P := hP.isNilpotent
      have hne : B.subgroupOf P ≠ ⊤ := fun h => (ne_of_lt hlt) (le_antisymm hBP
        (fun x hx => (Subgroup.mem_subgroupOf).mp (h ▸ Subgroup.mem_top (⟨x, hx⟩ : P))))
      obtain ⟨Q, hQ, hBQ⟩ : ∃ Q : Subgroup P, IsCoatom Q ∧ B.subgroupOf P ≤ Q := by
        rcases eq_top_or_exists_le_coatom (B.subgroupOf P) with h | h
        · exact absurd h hne
        · exact h
      have hQn : Q.Normal :=
        Subgroup.NormalizerCondition.normal_of_coatom Q Group.normalizerCondition_of_isNilpotent hQ
      set A : Subgroup G := Q.map P.subtype with hA
      have hAP : A ≤ P := Subgroup.map_subtype_le Q
      have hBA : B ≤ A := fun b hb =>
        Subgroup.mem_map.2 ⟨⟨b, hBP hb⟩, hBQ (Subgroup.mem_subgroupOf.2 hb), rfl⟩
      have hAsub : A.subgroupOf P = Q := by
        ext x
        constructor
        · intro hx
          obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
          have : q = x := Subtype.ext hqx
          rw [← this]
          exact hq
        · intro hx
          exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
      have hcoatA : IsCoatom (A.subgroupOf P) := by
        rw [hAsub]
        exact hQ
      have hAn : ∀ g ∈ P, ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
        intro g hg a ha
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 ha
        exact Subgroup.mem_map.2 ⟨⟨g, hg⟩ * q * (⟨g, hg⟩ : P)⁻¹,
          Subgroup.Normal.conj_mem hQn q hq ⟨g, hg⟩, by simp⟩
      have hφ : ∀ b ∈ P, ∃ a ∈ A, φ b = φ a := by
        intro b hb
        obtain ⟨β, hβ, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hPN hb)
        refine ⟨β, hBA hβ, ?_⟩
        rw [map_mul, (MonoidHom.mem_ker).1 hm, mul_one]
      have hAPlt : A < P := by
        refine lt_of_le_of_ne hAP fun h => hQ.1 ((Subgroup.eq_top_iff' Q).mpr fun x => ?_)
        have hxA : (x : G) ∈ A := by rw [h]; exact x.2
        obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.1 hxA
        have : q = x := Subtype.ext hqx
        rw [← this]
        exact hq
      have hcardA : Nat.card A ≤ n := by
        have h1 : Nat.card A ≤ Nat.card P := Subgroup.card_le_of_le hAP
        have h2 : Nat.card A ≠ Nat.card P := fun h =>
          (ne_of_lt hAPlt) (Subgroup.eq_of_le_of_card_ge hAP h.symm.le)
        omega
      have hstep : (GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G))).map φ ≤
          (GLAPPrimeCoreOf p (Subgroup.centralizer (P : Set G))).map φ :=
        map_GLAPPrimeCoreOf_centralizer_of_coatom φ hp hAP hP hcoatA hAn hφ
      exact (ih hcardA hBA (hP.to_le hAP) (hAP.trans hPN)).trans hstep

theorem map_glaPPrimeCoreOf_centralizer_le {X Z : Type*} [Group X] [Finite X] [Group Z]
    (φ : X →* Z) (hφ : Function.Surjective φ) {p : ℕ} (hp : p.Prime) {Q : Subgroup X}
    (hQ : IsPGroup p Q) :
    (GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set X))).map φ ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ((Q.map φ : Subgroup Z) : Set Z)) := by
  have : Finite Z := Finite.of_surjective φ hφ
  have : Fact p.Prime := ⟨hp⟩
  set T : Subgroup X := Q ⊔ φ.ker with hT
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (p := p) (P := Q.subgroupOf T)
    (hQ.comap_of_injective _ T.subtype_injective)
  set P : Subgroup X := (S : Subgroup T).map T.subtype with hP_def
  have hQT : Q ≤ T := le_sup_left
  have hPT : P ≤ T := Subgroup.map_subtype_le _
  have hQP : Q ≤ P := fun b hb =>
    Subgroup.mem_map.2 ⟨⟨b, hQT hb⟩, hS (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hPp : IsPGroup p P := S.isPGroup'.map _
  have hPN : P ≤ Q ⊔ φ.ker := hPT
  have hchain := map_GLAPPrimeCoreOf_centralizer_le_of_le φ hp _ le_rfl hQP hPp hPN
  have hsub : (GLAPPrimeCoreOf p (Subgroup.centralizer (P : Set X))).map φ ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ((Q.map φ : Subgroup Z) : Set Z)) := by
    refine le_GLAPPrimeCoreOf_of_normal ?_ ?_ ?_
    ·
      rintro _ ⟨u, hu, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have huQ : u ∈ Subgroup.centralizer (Q : Set X) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQP) (GLAPPrimeCoreOf_le _ hu)
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp huQ b hb]
    ·
      intro c hc x hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨y, rfl⟩ := hφ c
      have hy : ∀ b ∈ Q, y * b * y⁻¹ * b⁻¹ ∈ φ.ker := by
        intro b hb
        have hcomm := Subgroup.mem_centralizer_iff.mp hc (φ b) (Subgroup.mem_map.2 ⟨b, hb, rfl⟩)
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact hcomm.symm
      obtain ⟨n, hn, hnorm⟩ :=
        exists_mul_mem_normalizer_of_commutator_mem_prime hp (N := φ.ker) (B := Q) (T := T) rfl
          S hS hy
      have hn1 : φ n = 1 := MonoidHom.mem_ker.1 hn
      refine Subgroup.mem_map.2 ⟨(n⁻¹ * y) * u * (n⁻¹ * y)⁻¹,
        GLAPPrimeCoreOf_conj_mem_of_mem_normalizer hp
          (mem_normalizer_centralizer_of_mem_normalizer hnorm) u hu, ?_⟩
      simp [map_mul, map_inv, hn1]
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ φ)
        (coprime_card_GLAPPrimeCoreOf hp (Subgroup.centralizer (P : Set X)))
  exact hchain.trans hsub

end CFSG.HardMathSupport.Timmesfeld.Proving

end
