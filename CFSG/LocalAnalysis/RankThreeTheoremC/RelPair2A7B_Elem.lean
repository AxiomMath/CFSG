module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Facts
public import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsOptimalRelPair.false_of_normalizer {p : ℕ} {M D R T H V : Subgroup G}
    (hopt : IsOptimalRelPair p M D R T H V) {V₁ Q J : Subgroup G} (hV₁2 : IsPGroup 2 V₁)
    (hDV₁ : D ≤ normalizer (V₁ : Set G)) (hV₁M : V₁ ≤ M) (hVV₁ : V < V₁) (hQ2 : IsPGroup 2 Q)
    (hQ : Q ≠ ⊥) (hDQ : D ≤ normalizer (Q : Set G)) (hV₁Q : V₁ ≤ normalizer (Q : Set G))
    (hJ : J ≤ normalizer (Q : Set G)) (hthree : p ∣ Nat.card (invariantTwoJoinIn D J)) : False := by
  have hbase : relPairBase R T ≤ V := hopt.pair.base_le
  have hcand : IsRelPairCandidate p D R T (normalizer (Q : Set G)) :=
    { twoLocal := ⟨Q, hQ, hQ2, rfl⟩
      base_le := sup_le (hbase.trans (hVV₁.le.trans hV₁Q)) hDQ
      not_coprime := hthree.trans (Subgroup.card_dvd_of_le (invariantTwoJoinIn_mono hJ)) }
  obtain ⟨V', hV₁V', hmax⟩ := exists_invariantTwoMaximalWithin_containing D
    (normalizer (Q : Set G) ⊓ M) V₁ (le_inf hV₁Q hV₁M) hV₁2 hDV₁
  have hpair : IsRelPairCandidatePair p M D R T (normalizer (Q : Set G)) V' :=
    ⟨hcand, hmax, hbase.trans (hVV₁.le.trans hV₁V')⟩
  have h1 := hopt.card_le _ V' hpair
  have h2 : Nat.card V₁ ≤ Nat.card V' := Subgroup.card_le_of_le hV₁V'
  have h3 : Nat.card V < Nat.card V₁ := by
    by_contra h
    exact hVV₁.ne (Subgroup.eq_of_le_of_card_ge hVV₁.le (not_lt.mp h))
  omega

def squareCommutator (S : Subgroup G) : Subgroup G :=
  closure {x | ∃ a ∈ S, ∃ b ∈ S, x = a ^ 2 ∨ x = a * b * a⁻¹ * b⁻¹}

omit [Finite G] in
theorem squareCommutator_le (S : Subgroup G) : squareCommutator S ≤ S := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨a, ha, b, hb, rfl | rfl⟩
  · exact S.pow_mem ha 2
  · exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)

omit [Finite G] in
theorem squareCommutator_mono {A B : Subgroup G} (h : A ≤ B) :
    squareCommutator A ≤ squareCommutator B := by
  refine closure_mono ?_
  rintro x ⟨a, ha, b, hb, hx⟩
  exact ⟨a, h ha, b, h hb, hx⟩

omit [Finite G] in
theorem map_squareCommutator_le (f : G →* G) (S : Subgroup G) :
    (squareCommutator S).map f ≤ squareCommutator (S.map f) := by
  rw [squareCommutator, MonoidHom.map_closure]
  refine closure_mono ?_
  rintro _ ⟨x, ⟨a, ha, b, hb, hx⟩, rfl⟩
  refine ⟨f a, Subgroup.mem_map_of_mem f ha, f b, Subgroup.mem_map_of_mem f hb, ?_⟩
  rcases hx with rfl | rfl
  · exact Or.inl (map_pow f a 2)
  · exact Or.inr (by simp)

omit [Finite G] in
theorem squareCommutator_map_le (f : G →* G) (S : Subgroup G) :
    squareCommutator (S.map f) ≤ (squareCommutator S).map f := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl | rfl⟩
  · exact ⟨a ^ 2, subset_closure ⟨a, ha, a, ha, Or.inl rfl⟩, map_pow f a 2⟩
  · exact ⟨a * b * a⁻¹ * b⁻¹, subset_closure ⟨a, ha, b, hb, Or.inr rfl⟩, by simp⟩

omit [Finite G] in
theorem mem_normalizer_squareCommutator {S : Subgroup G} {g : G}
    (hg : g ∈ normalizer (S : Set G)) : g ∈ normalizer (squareCommutator S : Set G) := by
  have key : ∀ h ∈ normalizer (S : Set G),
      (squareCommutator S).map (MulAut.conj h).toMonoidHom ≤ squareCommutator S := by
    intro h hh
    have h1 := map_squareCommutator_le (MulAut.conj h).toMonoidHom S
    have hS : S.map (MulAut.conj h).toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp hh
    rwa [hS] at h1
  refine mem_normalizer_iff_map_conj_eq.mpr (le_antisymm (key g hg) ?_)
  intro x hx
  refine ⟨g⁻¹ * x * g, key g⁻¹ (inv_mem hg) ⟨x, hx, ?_⟩, ?_⟩
  · simp
  · simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem isElemAbelian_of_squareCommutator_eq_bot {S : Subgroup G}
    (h : squareCommutator S = ⊥) : IsElemAbelian 2 S := by
  have hmem : ∀ a ∈ S, ∀ b ∈ S, a ^ 2 = 1 ∧ a * b * a⁻¹ * b⁻¹ = 1 := by
    intro a ha b hb
    have h1 : a ^ 2 ∈ squareCommutator S := subset_closure ⟨a, ha, a, ha, Or.inl rfl⟩
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ squareCommutator S :=
      subset_closure ⟨a, ha, b, hb, Or.inr rfl⟩
    rw [h, Subgroup.mem_bot] at h1 h2
    exact ⟨h1, h2⟩
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => (hmem x hx x hx).1⟩
  apply Subtype.ext
  have h1 := (hmem x x.2 y y.2).2
  calc (x : G) * y = (x * y * (x : G)⁻¹ * (y : G)⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

omit [Finite G] in
theorem mem_normalizer_closure_of_forall {s : Set G} {g : G}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ closure s) (h' : ∀ x ∈ s, g⁻¹ * x * g ∈ closure s) :
    g ∈ normalizer (closure s : Set G) := by
  have key : ∀ k : G, (∀ x ∈ s, k * x * k⁻¹ ∈ closure s) →
      (closure s).map (MulAut.conj k).toMonoidHom ≤ closure s := by
    intro k hk
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hk x hx
  refine mem_normalizer_iff_map_conj_eq.mpr (le_antisymm (key g h) ?_)
  intro x hx
  have hh : ∀ y ∈ s, g⁻¹ * y * g⁻¹⁻¹ ∈ closure s := by simpa using h'
  have h2 := key g⁻¹ hh (Subgroup.mem_map_of_mem _ hx)
  refine ⟨g⁻¹ * x * g, by simpa using h2, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem mem_sup_iff_of_commute {K L : Subgroup G} (hc : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k)
    {x : G} : x ∈ K ⊔ L ↔ ∃ k ∈ K, ∃ l ∈ L, x = k * l := by
  constructor
  · intro hx
    let P : Subgroup G :=
      { carrier := {x | ∃ k ∈ K, ∃ l ∈ L, x = k * l}
        one_mem' := ⟨1, K.one_mem, 1, L.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨k, hk, l, hl, rfl⟩ ⟨k', hk', l', hl', rfl⟩
          refine ⟨k * k', K.mul_mem hk hk', l * l', L.mul_mem hl hl', ?_⟩
          have h1 : l * k' = k' * l := (hc k' hk' l hl).symm
          calc k * l * (k' * l') = k * (l * k') * l' := by group
            _ = k * (k' * l) * l' := by rw [h1]
            _ = k * k' * (l * l') := by group
        inv_mem' := by
          rintro _ ⟨k, hk, l, hl, rfl⟩
          refine ⟨k⁻¹, K.inv_mem hk, l⁻¹, L.inv_mem hl, ?_⟩
          have h1 : l⁻¹ * k⁻¹ = k⁻¹ * l⁻¹ := by
            have := hc k hk l hl
            calc l⁻¹ * k⁻¹ = (k * l)⁻¹ := by group
              _ = (l * k)⁻¹ := by rw [this]
              _ = k⁻¹ * l⁻¹ := by group
          rw [mul_inv_rev, h1] }
    have hKP : K ≤ P := fun k hk => ⟨k, hk, 1, L.one_mem, by simp⟩
    have hLP : L ≤ P := fun l hl => ⟨1, K.one_mem, l, hl, by simp⟩
    exact sup_le hKP hLP hx
  · rintro ⟨k, hk, l, hl, rfl⟩
    exact Subgroup.mul_mem_sup hk hl

omit [Finite G] in
theorem commutator_mul_left_of_commute {u c b : G} (hc : Commute u c) (hb : Commute u b) :
    u * c * b * (u * c)⁻¹ * b⁻¹ = c * b * c⁻¹ * b⁻¹ := by
  have h1 : Commute u (c * b * c⁻¹) := (hc.mul_right hb).mul_right hc.inv_right
  calc u * c * b * (u * c)⁻¹ * b⁻¹ = (u * (c * b * c⁻¹) * u⁻¹) * b⁻¹ := by group
    _ = c * b * c⁻¹ * b⁻¹ := by rw [h1.mul_inv_cancel]

omit [Finite G] in
theorem commutator_mul_right_of_commute {u c b : G} (hc : Commute u c) (hb : Commute u b) :
    c * (u * b) * c⁻¹ * (u * b)⁻¹ = c * b * c⁻¹ * b⁻¹ := by
  have h1 : Commute u (c * b * c⁻¹ * b⁻¹) :=
    ((hc.mul_right hb).mul_right hc.inv_right).mul_right hb.inv_right
  have hcu : c * u = u * c := hc.symm.eq
  calc c * (u * b) * c⁻¹ * (u * b)⁻¹ = (c * u) * b * c⁻¹ * b⁻¹ * u⁻¹ := by group
    _ = (u * c) * b * c⁻¹ * b⁻¹ * u⁻¹ := by rw [hcu]
    _ = u * (c * b * c⁻¹ * b⁻¹) * u⁻¹ := by group
    _ = c * b * c⁻¹ * b⁻¹ := h1.mul_inv_cancel

theorem IsOptimalRelPair.isElemAbelian_pCoreOf {M D R T H V : Subgroup G}
    (hopt : IsOptimalRelPair 3 M D R T H V) (hfacts : OptimalRelPairFacts 3 M D H V)
    {J₁ U : Subgroup G} (hdata : A7ModuleData D H V J₁ U)
    (hcard : Nat.card V = 4 * Nat.card (pCoreOf 2 H)) {T'' : Subgroup G} (hT''M : T'' ≤ M)
    (hT''2 : IsPGroup 2 T'') (hDT'' : D ≤ normalizer (T'' : Set G)) (hVT'' : V < T'') :
    IsElemAbelian 2 (pCoreOf 2 H) := by
  classical
  set S₀ : Subgroup G := pCoreOf 2 H with hS₀
  have hS₀2 : IsPGroup 2 S₀ := pCoreOf_isPGroup 2 H
  have hSV : S₀ ≤ V := hfacts.pCore_le
  have hVH : V ≤ H := hfacts.maximal.1
  have hDV : D ≤ normalizer (V : Set G) := hfacts.maximal.2.2.1
  have hHn : normalizer (S₀ : Set G) = H := hfacts.normalizer_pCore
  have hDH : D ≤ H := hdata.D_le.trans hdata.J₁_le
  have hHΦ : H ≤ normalizer (squareCommutator S₀ : Set G) := fun h hh =>
    mem_normalizer_squareCommutator (hHn ▸ hh)
  have hU0 : U ≠ ⊥ := by
    intro h
    have := hdata.card_U
    rw [h, Subgroup.card_bot] at this
    omega
  have hUS : U ≤ S₀ := hdata.U_le
  let 𝒱 : Set (Subgroup G) :=
    {Y | V < Y ∧ Y ≤ T'' ⊓ normalizer (V : Set G) ∧ D ≤ normalizer (Y : Set G)}
  have h𝒱 : (T'' ⊓ normalizer (V : Set G)) ∈ 𝒱 := by
    refine ⟨pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two T'' V hT''2 hVT'',
      le_rfl, ?_⟩
    have hDN : D ≤ normalizer ((normalizer (V : Set G) : Subgroup G) : Set G) :=
      fun d hd => Subgroup.le_normalizer (hDV hd)
    exact (le_inf hDT'' hDN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hne : ∃ n, ∃ Y ∈ 𝒱, Nat.card Y = n := ⟨_, _, h𝒱, rfl⟩
  obtain ⟨V₁, hV₁, hcard₁⟩ := Nat.find_spec hne
  have hmin : ∀ Y ∈ 𝒱, Nat.card V₁ ≤ Nat.card Y := fun Y hY => by
    have := Nat.find_min' hne ⟨Y, hY, rfl⟩
    omega
  obtain ⟨hVV₁, hV₁T, hDV₁⟩ := hV₁
  have hV₁2 : IsPGroup 2 V₁ := hT''2.to_le (hV₁T.trans inf_le_left)
  have hV₁M : V₁ ≤ M := hV₁T.trans (inf_le_left.trans hT''M)
  have hV₁N : V₁ ≤ normalizer (V : Set G) := hV₁T.trans inf_le_right
  by_cases hA : ∀ y ∈ V₁, ∀ u ∈ U, y * u * y⁻¹ ∈ S₀
  ·
    exfalso
    set s : Set G := {x | ∃ y ∈ V₁, ∃ u ∈ U, x = y * u * y⁻¹} with hs
    set V₀ : Subgroup G := closure s with hV₀
    have hV₀S : V₀ ≤ S₀ := (Subgroup.closure_le _).mpr (by
      rintro _ ⟨y, hy, u, hu, rfl⟩
      exact hA y hy u hu)
    have hUV₀ : U ≤ V₀ := fun u hu => subset_closure ⟨1, V₁.one_mem, u, hu, by simp⟩
    have hV₀0 : V₀ ≠ ⊥ := fun h => hU0 (le_bot_iff.mp (h ▸ hUV₀))
    have hV₁V₀ : V₁ ≤ normalizer (V₀ : Set G) := by
      intro y' hy'
      refine mem_normalizer_closure_of_forall ?_ ?_
      · rintro _ ⟨y, hy, u, hu, rfl⟩
        exact subset_closure ⟨y' * y, V₁.mul_mem hy' hy, u, hu, by group⟩
      · rintro _ ⟨y, hy, u, hu, rfl⟩
        exact subset_closure ⟨y'⁻¹ * y, V₁.mul_mem (V₁.inv_mem hy') hy, u, hu, by group⟩
    have hDV₀ : D ≤ normalizer (V₀ : Set G) := by
      intro d hd
      have hdinv : d⁻¹ ∈ D := D.inv_mem hd
      refine mem_normalizer_closure_of_forall ?_ ?_
      · rintro _ ⟨y, hy, u, hu, rfl⟩
        exact subset_closure ⟨d * y * d⁻¹, (mem_normalizer_iff.mp (hDV₁ hd) y).mp hy,
          d * u * d⁻¹, (mem_normalizer_iff.mp (hdata.U_normal (hDH hd)) u).mp hu, by group⟩
      · rintro _ ⟨y, hy, u, hu, rfl⟩
        exact subset_closure ⟨d⁻¹ * y * d⁻¹⁻¹, (mem_normalizer_iff.mp (hDV₁ hdinv) y).mp hy,
          d⁻¹ * u * d⁻¹⁻¹, (mem_normalizer_iff.mp (hdata.U_normal (hDH hdinv)) u).mp hu,
          by group⟩
    have hJV₀ : J₁ ≤ normalizer (V₀ : Set G) := by
      have key : ∀ j ∈ J₁, ∀ x ∈ V₀, j * x * j⁻¹ ∈ V₀ := by
        intro j hj x hx
        have hu : x * j * x⁻¹ * j⁻¹ ∈ U := hdata.comm x (hV₀S hx) j hj
        have : j * x * j⁻¹ = (x * j * x⁻¹ * j⁻¹)⁻¹ * x := by group
        rw [this]
        exact V₀.mul_mem (V₀.inv_mem (hUV₀ hu)) hx
      intro j hj
      refine mem_normalizer_closure_of_forall
        (fun x hx => key j hj x (subset_closure hx)) (fun x hx => ?_)
      simpa using key j⁻¹ (J₁.inv_mem hj) x (subset_closure hx)
    exact hopt.false_of_normalizer hV₁2 hDV₁ hV₁M hVV₁ (hS₀2.to_le hV₀S) hV₀0 hDV₀ hV₁V₀ hJV₀
      hdata.three
  ·
    push Not at hA
    obtain ⟨y, hyV₁, u₀, hu₀, hyu₀⟩ := hA
    have hyN : y ∈ normalizer (V : Set G) := hV₁N hyV₁
    have hyV : y ∉ V := fun hyVV =>
      hyu₀ (hUS ((mem_normalizer_iff.mp (hdata.U_normal (hVH hyVV)) u₀).mp hu₀))
    set cy : G →* G := (MulAut.conj y).toMonoidHom with hcy
    have hcyinj : Function.Injective cy := (MulAut.conj y).injective
    have hcyapp : ∀ g : G, cy g = y * g * y⁻¹ := fun g => by simp [hcy, MulAut.conj_apply]
    set S₀y : Subgroup G := S₀.map cy with hS₀y
    have hVy : V.map cy = V := mem_normalizer_iff_map_conj_eq.mp hyN
    have hS₀yV : S₀y ≤ V := hVy ▸ Subgroup.map_mono hSV
    have hcardS₀y : Nat.card S₀y = Nat.card S₀ := Subgroup.card_map_of_injective hcyinj
    set C : Subgroup G := S₀ ⊓ S₀y with hC
    have hCS : C ≤ S₀ := inf_le_left
    have hCy : C ≤ S₀y := inf_le_right
    have hS₀pos : 0 < Nat.card S₀ := Nat.card_pos
    have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := S₀) (B := S₀y) (hS₀yV.trans (hVH.trans hHn.ge))
    have hsupV : Nat.card (S₀ ⊔ S₀y : Subgroup G) ≤ Nat.card V :=
      Subgroup.card_le_of_le (sup_le hSV hS₀yV)
    have h4C : Nat.card S₀ ≤ 4 * Nat.card C := by
      have h1 : Nat.card S₀ * Nat.card S₀ ≤ Nat.card S₀ * (4 * Nat.card C) := by
        calc Nat.card S₀ * Nat.card S₀ = Nat.card S₀ * Nat.card S₀y := by rw [hcardS₀y]
          _ = Nat.card (S₀ ⊔ S₀y : Subgroup G) * Nat.card C := hprod.symm
          _ ≤ Nat.card V * Nat.card C := Nat.mul_le_mul_right _ hsupV
          _ = Nat.card S₀ * (4 * Nat.card C) := by rw [hcard]; ring
      exact Nat.le_of_mul_le_mul_left h1 hS₀pos
    have hCUV : Nat.card (U ⊓ centralizer (V : Set G) : Subgroup G) = 4 := by
      have h1 := hdata.idx
      have h2 := hdata.card_U
      omega
    have hx₀V : y * u₀ * y⁻¹ ∈ V := (mem_normalizer_iff.mp hyN u₀).mp (hSV (hUS hu₀))
    have hUC : U ⊓ C ≤ U ⊓ centralizer (V : Set G) := by
      intro w hw
      have hwU : w ∈ U := hw.1
      obtain ⟨s, hs, hsw⟩ := hw.2.2
      have hw' : w = y * s * y⁻¹ := by rw [← hsw, hcyapp]
      have hss : s * u₀ = u₀ * s := mem_centralizer_iff.mp (hdata.U_central hu₀) s hs
      have hcomm : (y * u₀ * y⁻¹) * w = w * (y * u₀ * y⁻¹) := by
        rw [hw']
        calc y * u₀ * y⁻¹ * (y * s * y⁻¹) = y * (u₀ * s) * y⁻¹ := by group
          _ = y * (s * u₀) * y⁻¹ := by rw [hss]
          _ = y * s * y⁻¹ * (y * u₀ * y⁻¹) := by group
      have hq := hdata.quad (y * u₀ * y⁻¹) hx₀V hyu₀
      have hwq : w ∈ U ⊓ centralizer ({y * u₀ * y⁻¹} : Set G) :=
        ⟨hwU, mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact hcomm⟩
      rw [hq] at hwq
      exact hwq
    have hUC4 : Nat.card (U ⊓ C : Subgroup G) ≤ 4 :=
      (Subgroup.card_le_of_le hUC).trans hCUV.le
    have hcommUC : ∀ k ∈ U, ∀ l ∈ C, k * l = l * k := fun k hk l hl =>
      (mem_centralizer_iff.mp (hdata.U_central hk) l (hCS hl)).symm
    have hCU : C ≤ normalizer (U : Set G) := fun l hl =>
      Subgroup.centralizer_le_normalizer _
        (mem_centralizer_iff.mpr fun k hk => hcommUC k hk l hl)
    have hprod2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := U) (B := C) hCU
    have hUCS : U ⊔ C = S₀ := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hUS hCS) ?_
      have h1 : Nat.card (U ⊔ C : Subgroup G) * Nat.card (U ⊓ C : Subgroup G) =
          16 * Nat.card C := by rw [hprod2, hdata.card_U]
      have h2 : Nat.card (U ⊔ C : Subgroup G) * Nat.card (U ⊓ C : Subgroup G) ≤
          Nat.card (U ⊔ C : Subgroup G) * 4 := Nat.mul_le_mul_left _ hUC4
      omega
    have hcen : ∀ v ∈ U, ∀ t ∈ S₀, Commute v t := fun v hv t ht =>
      (mem_centralizer_iff.mp (hdata.U_central hv) t ht).symm
    set Φ : Subgroup G := squareCommutator S₀ with hΦ
    have hΦle : Φ ≤ squareCommutator C := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨a, ha, b, hb, rfl | rfl⟩
      · obtain ⟨u, hu, c, hc, rfl⟩ := (mem_sup_iff_of_commute hcommUC).mp (by rw [hUCS]; exact ha)
        rw [(hcen u hu c (hCS hc)).mul_pow, hdata.U_exp u hu, one_mul]
        exact subset_closure ⟨c, hc, c, hc, Or.inl rfl⟩
      · obtain ⟨u, hu, c, hc, rfl⟩ := (mem_sup_iff_of_commute hcommUC).mp (by rw [hUCS]; exact ha)
        obtain ⟨u', hu', c', hc', rfl⟩ :=
          (mem_sup_iff_of_commute hcommUC).mp (by rw [hUCS]; exact hb)
        rw [commutator_mul_left_of_commute (hcen u hu c (hCS hc))
          ((hcen u hu u' (hUS hu')).mul_right (hcen u hu c' (hCS hc'))),
          commutator_mul_right_of_commute (hcen u' hu' c (hCS hc)) (hcen u' hu' c' (hCS hc'))]
        exact subset_closure ⟨c, hc, c', hc', Or.inr rfl⟩
    have hΦmap : Φ ≤ Φ.map cy :=
      hΦle.trans ((squareCommutator_mono hCy).trans (squareCommutator_map_le cy S₀))
    have hΦcard : Nat.card (Φ.map cy) = Nat.card Φ := Subgroup.card_map_of_injective hcyinj
    have hΦeq : Φ = Φ.map cy := Subgroup.eq_of_le_of_card_ge hΦmap hΦcard.le
    have hyΦ : y ∈ normalizer (Φ : Set G) := mem_normalizer_iff_map_conj_eq.mpr hΦeq.symm
    set N₁ : Subgroup G := V₁ ⊓ normalizer (Φ : Set G) with hN₁def
    have hVN₁ : V ≤ N₁ := le_inf hVV₁.le (hVH.trans hHΦ)
    have hN₁ : N₁ ∈ 𝒱 := by
      refine ⟨lt_of_le_of_ne hVN₁ ?_, inf_le_left.trans hV₁T, ?_⟩
      · intro heq
        have hyN₁ : y ∈ N₁ := ⟨hyV₁, hyΦ⟩
        rw [← heq] at hyN₁
        exact hyV hyN₁
      · have hDΦ : D ≤ normalizer ((normalizer (Φ : Set G) : Subgroup G) : Set G) :=
          fun d hd => Subgroup.le_normalizer (hHΦ (hDH hd))
        exact (le_inf hDV₁ hDΦ).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hN₁V₁ : N₁ = V₁ := Subgroup.eq_of_le_of_card_ge inf_le_left (hmin N₁ hN₁)
    have hV₁Φ : V₁ ≤ normalizer (Φ : Set G) := fun v hv => by
      rw [← hN₁V₁] at hv
      exact hv.2
    by_contra hnot
    have hΦ0 : Φ ≠ ⊥ := fun h => hnot (isElemAbelian_of_squareCommutator_eq_bot h)
    exact hopt.false_of_normalizer hV₁2 hDV₁ hV₁M hVV₁ (hS₀2.to_le (squareCommutator_le S₀)) hΦ0
      (hDH.trans hHΦ) hV₁Φ (hdata.J₁_le.trans hHΦ) hdata.three

end CFSG.LocalAnalysis.RankThreeTheoremC
