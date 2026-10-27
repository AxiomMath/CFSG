module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.InducedAux

section Bar
variable {X : Type} [Group X] {W K : Subgroup X} [W.Normal]

theorem toBar_coe (k : ↥K) : ((toBar W K k : ↥(bar W K)) : X ⧸ W) = QuotientGroup.mk (k : X) := rfl

theorem toBar_surjective : Function.Surjective (toBar W K) := by
  rintro ⟨y, k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩

theorem toBar_eq_one_iff {k : ↥K} : toBar W K k = 1 ↔ (k : X) ∈ W := by
  rw [← Subtype.coe_inj, toBar_coe, Subgroup.coe_one, QuotientGroup.eq_one_iff]

theorem comm_mem_iff' {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (b k : G) :
    ⁅b, k⁆ ∈ N ↔ (QuotientGroup.mk b : G ⧸ N) * QuotientGroup.mk k =
      QuotientGroup.mk k * QuotientGroup.mk b := by
  rw [← QuotientGroup.eq_one_iff, ← commutatorElement_eq_one_iff_mul_comm]
  exact Iff.rfl

theorem comm_mem_iff (b k : X) :
    ⁅b, k⁆ ∈ W ↔ (QuotientGroup.mk b : X ⧸ W) * QuotientGroup.mk k =
      QuotientGroup.mk k * QuotientGroup.mk b := comm_mem_iff' W b k

theorem mk_mem_normalizer_bar {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) :
    (QuotientGroup.mk b : X ⧸ W) ∈
      Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  induction n using QuotientGroup.induction_on with
  | H x =>
    have e : (QuotientGroup.mk b : X ⧸ W) * QuotientGroup.mk x * (QuotientGroup.mk b)⁻¹ =
        QuotientGroup.mk (b * x * b⁻¹) := by simp
    rw [e]
    simp only [SetLike.mem_coe, Subgroup.mem_map, QuotientGroup.mk'_apply]
    constructor
    · rintro ⟨k, hk, hkx⟩
      refine ⟨b * k * b⁻¹, ((Subgroup.mem_normalizer_iff.mp hb) k).mp hk, ?_⟩
      simp [hkx]
    · rintro ⟨k, hk, hkx⟩
      refine ⟨b⁻¹ * k * b, ?_, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp hb) (b⁻¹ * k * b)
        rw [show b * (b⁻¹ * k * b) * b⁻¹ = k by group] at h1
        exact h1.mpr hk
      · have h2 : (QuotientGroup.mk b : X ⧸ W) * QuotientGroup.mk x * (QuotientGroup.mk b)⁻¹ =
            QuotientGroup.mk k := by rw [e]; exact hkx.symm
        have h3 : (QuotientGroup.mk x : X ⧸ W) =
            (QuotientGroup.mk b)⁻¹ * QuotientGroup.mk k * QuotientGroup.mk b := by
          rw [← h2]; group
        rw [h3]; simp

@[expose] noncomputable def indHom (W K B : Subgroup X) [W.Normal]
    (hB : B ≤ Subgroup.normalizer (K : Set X)) : ↥B →* MulAut ↥(bar W K) :=
  (bar W K).normalizerMonoidHom.comp
    (((QuotientGroup.mk' W).comp B.subtype).codRestrict _
      (fun b => mk_mem_normalizer_bar (hB b.2)))

theorem indHom_apply (B : Subgroup X) (hB : B ≤ Subgroup.normalizer (K : Set X)) (b : ↥B) :
    indHom W K B hB b = (bar W K).normalizerMonoidHom
      ⟨QuotientGroup.mk (b : X), mk_mem_normalizer_bar (hB b.2)⟩ := rfl

theorem indHom_toBar (B : Subgroup X) (hB : B ≤ Subgroup.normalizer (K : Set X)) (b : ↥B) (k : ↥K) :
    ((indHom W K B hB b (toBar W K k) : ↥(bar W K)) : X ⧸ W) =
      QuotientGroup.mk ((b : X) * k * (b : X)⁻¹) := by
  rw [indHom_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  simp [toBar_coe]

theorem indHom_eq_one_iff (B : Subgroup X) (hB : B ≤ Subgroup.normalizer (K : Set X)) (b : ↥B) :
    indHom W K B hB b = 1 ↔ ∀ k ∈ K, ⁅(b : X), k⁆ ∈ W := by
  constructor
  · intro h k hk
    have h1 := congrArg (fun φ : MulAut ↥(bar W K) => ((φ (toBar W K ⟨k, hk⟩) : ↥(bar W K)) : X ⧸ W)) h
    simp only [indHom_toBar, MulAut.one_apply, toBar_coe] at h1
    rw [comm_mem_iff]
    have h2 : (QuotientGroup.mk (b : X) : X ⧸ W) * QuotientGroup.mk k * (QuotientGroup.mk (b : X))⁻¹ =
        QuotientGroup.mk k := by
      simpa using h1
    calc (QuotientGroup.mk (b : X) : X ⧸ W) * QuotientGroup.mk k
        = (QuotientGroup.mk (b : X) * QuotientGroup.mk k * (QuotientGroup.mk (b : X))⁻¹) *
            QuotientGroup.mk (b : X) := by group
      _ = _ := by rw [h2]
  · intro h
    ext y
    obtain ⟨k, rfl⟩ := toBar_surjective y
    rw [indHom_toBar, MulAut.one_apply, toBar_coe]
    have h1 := (comm_mem_iff _ _).mp (h k k.2)
    calc (QuotientGroup.mk ((b : X) * k * (b : X)⁻¹) : X ⧸ W)
        = QuotientGroup.mk (b : X) * QuotientGroup.mk (k : X) * (QuotientGroup.mk (b : X))⁻¹ := by simp
      _ = QuotientGroup.mk (k : X) := by rw [h1]; group

theorem range_indHom (B : Subgroup X) (hB : B ≤ Subgroup.normalizer (K : Set X)) :
    (indHom W K B hB).range = indAut W K B := by
  ext φ
  simp only [MonoidHom.mem_range, indAut, inducedAutGroup, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨⟨QuotientGroup.mk (b : X), mk_mem_normalizer_bar (hB b.2)⟩, ⟨b, b.2, rfl⟩, rfl⟩
  · rintro ⟨⟨y, hyN⟩, ⟨b, hbB, hby⟩, rfl⟩
    refine ⟨⟨b, hbB⟩, ?_⟩
    simp only [indHom, MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext hby

end Bar

section Ind
variable {X : Type} [Group X] {W K S : Subgroup X} [W.Normal]

theorem indHom_mem (h : Setup28 W K S) {a : X} (haS : a ∈ S) :
    indHom W K S h.hN ⟨a, haS⟩ ∈ indAut W K S := by
  rw [← range_indHom S h.hN]
  exact ⟨_, rfl⟩

theorem indHom_of_indInner (h : Setup28 W K S) {a : X} (haS : a ∈ S) {k : X} (hk : k ∈ K)
    (hik : ∀ x ∈ K, a * x * a⁻¹ * (k * x * k⁻¹)⁻¹ ∈ W) :
    indHom W K S h.hN ⟨a, haS⟩ = MulAut.conj (toBar W K ⟨k, hk⟩) := by
  ext y
  obtain ⟨x, rfl⟩ := toBar_surjective y
  rw [indHom_toBar]
  change _ = ((toBar W K ⟨k, hk⟩ * toBar W K x * (toBar W K ⟨k, hk⟩)⁻¹ : ↥(bar W K)) : X ⧸ W)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, toBar_coe]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact QuotientGroup.eq_iff_div_mem.mpr (by simpa [div_eq_mul_inv] using hik x x.2)

theorem mem_kerAct_of_indHom_eq_one (h : Setup28 W K S) {a : X} (haS : a ∈ S)
    (h1 : indHom W K S h.hN ⟨a, haS⟩ = 1) : a ∈ kerAct W K S :=
  ⟨haS, (indHom_eq_one_iff S h.hN ⟨a, haS⟩).mp h1⟩

end Ind

section CardInd
variable {X : Type} [Group X] {W K S : Subgroup X} [W.Normal]

theorem ker_indHom (h : Setup28 W K S) {B : Subgroup X} (hB : B ≤ S) :
    (indHom W K B (hB.trans h.hN)).ker = (kerAct W K S).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, indHom_eq_one_iff, Subgroup.mem_subgroupOf]
  exact ⟨fun hb => ⟨hB b.2, hb⟩, fun hb => hb.2⟩

theorem card_indAut (h : Setup28 W K S) {B : Subgroup X} (hB : B ≤ S) :
    Nat.card ↥(indAut W K B) = (kerAct W K S).relIndex B := by
  rw [← range_indHom B (hB.trans h.hN), ← Subgroup.index_ker, ker_indHom h hB]
  rfl

end CardInd

section Pure

theorem exists_transv_of_relIndex_two {X : Type*} [Group X] (V : Subgroup X)
    (hsq : ∀ v ∈ V, v ^ 2 = 1) (a : X) (hnorm : ∀ v ∈ V, a * v * a⁻¹ ∈ V)
    (h2 : (Subgroup.centralizer ({a} : Set X)).relIndex V = 2) :
    ∃ u ∈ V, u ≠ 1 ∧ ∀ v ∈ V, a * v * a⁻¹ = v ∨ a * v * a⁻¹ = v * u := by
  have h2' : ((Subgroup.centralizer ({a} : Set X)).subgroupOf V).index = 2 := h2
  obtain ⟨b₀, hb₀⟩ := Subgroup.index_eq_two_iff.mp h2'
  set Hv := (Subgroup.centralizer ({a} : Set X)).subgroupOf V with hHv
  have hmem : ∀ v : V, v ∈ Hv ↔ a * (v : X) = (v : X) * a := by
    intro v
    rw [hHv, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    simp
  have hb₀n : b₀ ∉ Hv := by
    have := hb₀ 1
    have h1 : (1 : V) ∈ Hv := Hv.one_mem
    simp only [one_mul] at this
    unfold Xor at this
    tauto
  have hu : a * (b₀ : X) * a⁻¹ * (b₀ : X)⁻¹ ∈ V := V.mul_mem (hnorm _ b₀.2) (V.inv_mem b₀.2)
  have hu2 : (a * (b₀ : X) * a⁻¹ * (b₀ : X)⁻¹)⁻¹ = a * (b₀ : X) * a⁻¹ * (b₀ : X)⁻¹ := by
    have := hsq _ hu
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  refine ⟨a * (b₀ : X) * a⁻¹ * (b₀ : X)⁻¹, hu, ?_, ?_⟩
  · intro h1
    apply hb₀n
    rw [hmem]
    have h3 : a * (b₀ : X) * a⁻¹ = b₀ := mul_inv_eq_one.mp h1
    calc a * (b₀ : X) = a * b₀ * a⁻¹ * a := by group
      _ = b₀ * a := by rw [h3]
  · intro v hv
    by_cases hvH : (⟨v, hv⟩ : V) ∈ Hv
    · left
      have h3 := (hmem _).mp hvH
      simp only at h3
      rw [h3]; group
    · right
      have hx := hb₀ ⟨v, hv⟩
      unfold Xor at hx
      have hvb : (⟨v, hv⟩ * b₀ : V) ∈ Hv := by tauto
      have hc := (hmem _).mp hvb
      simp only [Subgroup.coe_mul] at hc
      have h4 : a * (v * b₀) * a⁻¹ = v * b₀ := by rw [hc]; group
      calc a * v * a⁻¹ = (a * (v * b₀) * a⁻¹) * (a * (b₀ : X)⁻¹ * a⁻¹) := by group
        _ = v * b₀ * (a * (b₀ : X)⁻¹ * a⁻¹) := by rw [h4]
        _ = v * (a * (b₀ : X) * a⁻¹ * (b₀ : X)⁻¹)⁻¹ := by group
        _ = v * (a * (b₀ : X) * a⁻¹ * (b₀ : X)⁻¹) := by rw [hu2]

theorem eq_top_of_perfect_of_sup_pGroup {G : Type*} [Group G] [Finite G] (hG : commutator G = ⊤)
    (M R : Subgroup G) [M.Normal] (hMR : M ⊔ R = ⊤) (hR : IsPGroup 2 ↥R) : M = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hG
  let φ : R →* G ⧸ M := (QuotientGroup.mk' M).comp R.subtype
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M x
    have hg : g ∈ R ⊔ M := by
      rw [sup_comm, hMR]
      exact Subgroup.mem_top g
    obtain ⟨r, hr, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    refine ⟨⟨r, hr⟩, ?_⟩
    show ((r : G) : G ⧸ M) = ((r * m : G) : G ⧸ M)
    rw [QuotientGroup.eq, inv_mul_cancel_left]
    exact hm
  have hQ : IsPGroup 2 (G ⧸ M) := hR.of_surjective φ hφ
  haveI : Finite (G ⧸ M) :=
    Finite.of_surjective (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
  haveI : Group.IsNilpotent (G ⧸ M) := IsPGroup.isNilpotent hQ
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable (G ⧸ M)).solvable
  have hsub : ∀ a : G ⧸ M, a = 1 := by
    intro a
    have ha : a ∈ derivedSeries (G ⧸ M) n := by
      rw [Group.IsPerfect.derivedSeries_eq_top (G ⧸ M) n]
      exact Subgroup.mem_top a
    rw [hn, Subgroup.mem_bot] at ha
    exact ha
  rw [eq_top_iff]
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (hsub (g : G ⧸ M))

theorem eq_top_of_quasisimple_normal {G : Type*} [Group G] (hG1 : commutator G = ⊤)
    (hG2 : IsSimpleGroup (G ⧸ Subgroup.center G)) (N : Subgroup G) [N.Normal]
    (hN : ¬ N ≤ Subgroup.center G) : N = ⊤ := by
  let π : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective (Subgroup.center G)
  have hNmap : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπsurj
  have hmap : N.map π = ⊤ := by
    rcases hG2.eq_bot_or_eq_top_of_normal (N.map π) with h | h
    · exfalso
      apply hN
      intro n hn
      have hmem : π n ∈ N.map π := Subgroup.mem_map_of_mem π hn
      rw [h, Subgroup.mem_bot] at hmem
      have h1 : (n : G ⧸ Subgroup.center G) = 1 := hmem
      exact (QuotientGroup.eq_one_iff n).mp h1
    · exact h
  have hdec : ∀ g : G, ∃ n ∈ N, ∃ z ∈ Subgroup.center G, g = n * z := by
    intro g
    have hg : π g ∈ N.map π := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hπn⟩ := Subgroup.mem_map.mp hg
    have hπn' : (n : G ⧸ Subgroup.center G) = (g : G ⧸ Subgroup.center G) := hπn
    have hz : n⁻¹ * g ∈ Subgroup.center G := QuotientGroup.eq.mp hπn'
    exact ⟨n, hn, n⁻¹ * g, hz, (mul_inv_cancel_left n g).symm⟩
  have hnh : ∀ n : G, n ∈ N → ∀ h : G, ⁅n, h⁆ ∈ N := by
    intro n hn h
    have hconj : h * n⁻¹ * h⁻¹ ∈ N :=
      Subgroup.Normal.conj_mem inferInstance n⁻¹ (N.inv_mem hn) h
    have h2 : ⁅n, h⁆ = n * (h * n⁻¹ * h⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact N.mul_mem hn hconj
  have hcen : ∀ n h z : G, z ∈ Subgroup.center G → ⁅n * z, h⁆ = ⁅n, h⁆ := by
    intro n h z hz
    have hc : h * z = z * h := Subgroup.mem_center_iff.mp hz h
    rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
    calc n * z * h * (z⁻¹ * n⁻¹) * h⁻¹ = n * (z * h * z⁻¹) * n⁻¹ * h⁻¹ := by group
      _ = n * (h * z * z⁻¹) * n⁻¹ * h⁻¹ := by rw [← hc]
      _ = n * h * n⁻¹ * h⁻¹ := by group
  have hcomm : commutator G ≤ N := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g _ h _
    obtain ⟨n, hn, z, hz, rfl⟩ := hdec g
    rw [hcen n h z hz]
    exact hnh n hn h
  rw [hG1] at hcomm
  exact top_le_iff.mp hcomm

@[expose] noncomputable def autCenterQuot (G : Type*) [Group G] :
    MulAut G →* MulAut (G ⧸ Subgroup.center G) where
  toFun α := QuotientGroup.congr (Subgroup.center G) (Subgroup.center G) α
    (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]

theorem autCenterQuot_mk {G : Type*} [Group G] (α : MulAut G) (x : G) :
    autCenterQuot G α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  QuotientGroup.congr_mk (Subgroup.center G) (Subgroup.center G) α (Subgroup.map_center_eq α) x

theorem four_le_of_equiv_alternatingGroup {G : Type*} [Group G] {m n : ℕ} (hm : 5 ≤ m)
    (e₀ : G ≃* alternatingGroup (Fin m)) (e : G ≃* alternatingGroup (Fin n)) : 4 ≤ n := by
  by_contra hn
  push_neg at hn
  have h1 : Nat.card (alternatingGroup (Fin m)) = Nat.card G := (Nat.card_congr e₀.toEquiv).symm
  have h2 : Nat.card (alternatingGroup (Fin n)) = Nat.card G := (Nat.card_congr e.toEquiv).symm
  have h3 : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp
  have h4 : Nat.card (alternatingGroup (Fin n)) ≤ n.factorial := by
    calc Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Equiv.Perm (Fin n)) :=
          Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective
      _ = n.factorial := by simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  have h5 : (5 : ℕ).factorial ≤ m.factorial := Nat.factorial_le hm
  have h6 : n.factorial ≤ (3 : ℕ).factorial := Nat.factorial_le (by omega)
  have h7 : (5 : ℕ).factorial = 120 := by decide
  have h8 : (3 : ℕ).factorial = 6 := by decide
  omega

theorem aut_eq_one {G : Type*} [Group G] (hG : commutator G = ⊤) {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) (α : MulAut G) (h : ∀ x : G, x⁻¹ * α x ∈ Z) : α = 1 := by
  have hc : ∀ x y : G, y * (x⁻¹ * α x) = (x⁻¹ * α x) * y := fun x y =>
    Subgroup.mem_center_iff.mp (hZ (h x)) y
  let f : G →* G :=
    { toFun := fun x => x⁻¹ * α x
      map_one' := by simp
      map_mul' := fun x y => by
        have := hc x y⁻¹
        simp only [mul_inv_rev, map_mul]
        calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [this]
          _ = _ := by group }
  have hker : commutator G ≤ f.ker := by
    show ⁅(⊤ : Subgroup G), ⊤⁆ ≤ f.ker
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc g₂ (f g₁)
  ext x
  have hx : x ∈ f.ker := hker (hG ▸ Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, inv_mul_eq_one] at hx
  simpa using hx.symm

theorem aut_mem_center {G : Type*} [Group G] (α : MulAut G) {z : G} (hz : z ∈ Subgroup.center G) :
    α z ∈ Subgroup.center G := by
  have := Subgroup.mem_map_of_mem (α : G →* G) hz
  rwa [show (Subgroup.center G).map (α : G →* G) = Subgroup.center G from
    Subgroup.map_center_eq α] at this

theorem autCenterQuot_injective {G : Type*} [Group G] (hG : commutator G = ⊤) :
    Function.Injective (autCenterQuot G) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  refine aut_eq_one hG le_rfl α fun x => ?_
  have h1 := congrArg (fun φ : MulAut (G ⧸ Subgroup.center G) => φ (QuotientGroup.mk x)) hα
  simp only [autCenterQuot_mk, MulAut.one_apply] at h1
  exact QuotientGroup.eq.mp h1.symm

theorem autCenterQuot_conj {G : Type*} [Group G] (g : G) :
    autCenterQuot G (MulAut.conj g) = MulAut.conj (QuotientGroup.mk g : G ⧸ Subgroup.center G) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x => simp [autCenterQuot_mk]

theorem card_le_of_induces {G K' : Type*} [Group G] [Group K'] (hG : commutator G = ⊤)
    (e : (G ⧸ Subgroup.center G) ≃* K') (F : Subgroup (MulAut G)) (T : Subgroup (MulAut K'))
    [Finite T] (hF : ∀ φ ∈ F, ∃ σ ∈ T, InducesOn e φ σ) : Nat.card F ≤ Nat.card T := by
  choose! σ hσT hσ using hF
  let f : F → T := fun φ => ⟨σ φ, hσT φ φ.2⟩
  refine Nat.card_le_card_of_injective f ?_
  intro φ₁ φ₂ hφ
  have hs : σ φ₁ = σ φ₂ := congrArg Subtype.val hφ
  have hmk : ∀ a : G, (QuotientGroup.mk ((φ₁ : MulAut G) a) : G ⧸ Subgroup.center G) =
      QuotientGroup.mk ((φ₂ : MulAut G) a) := by
    intro a
    apply e.injective
    rw [hσ φ₁ φ₁.2 a, hσ φ₂ φ₂.2 a, hs]
  have hα : (φ₁ : MulAut G)⁻¹ * (φ₂ : MulAut G) = 1 := by
    refine aut_eq_one hG le_rfl _ fun a => ?_
    have h1 : ((φ₁ : MulAut G) a)⁻¹ * (φ₂ : MulAut G) a ∈ Subgroup.center G :=
      QuotientGroup.eq.mp (hmk a)
    have h2 := aut_mem_center (φ₁ : MulAut G)⁻¹ h1
    have e1 : (φ₁ : MulAut G)⁻¹ (((φ₁ : MulAut G) a)⁻¹ * (φ₂ : MulAut G) a) =
        a⁻¹ * ((φ₁ : MulAut G)⁻¹ * (φ₂ : MulAut G)) a := by
      rw [map_mul, map_inv, MulAut.inv_apply_self, MulAut.mul_apply]
    rwa [e1] at h2
  apply Subtype.ext
  exact inv_mul_eq_one.mp hα

end Pure

section Normal
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem zPre_iff (k : ↥K) : (k : X) ∈ zPre W K ↔ toBar W K k ∈ Subgroup.center ↥(bar W K) := by
  rw [Subgroup.mem_center_iff]
  constructor
  · rintro ⟨_, hk⟩ y
    obtain ⟨k', rfl⟩ := toBar_surjective y
    apply Subtype.ext
    simp only [Subgroup.coe_mul, toBar_coe]
    exact ((comm_mem_iff _ _).mp (hk k' k'.2)).symm
  · intro hk
    refine ⟨k.2, fun k' hk' => ?_⟩
    rw [comm_mem_iff]
    have := congrArg Subtype.val (hk (toBar W K ⟨k', hk'⟩))
    simpa [toBar_coe] using this.symm

theorem commutator_K (h : Setup28 W K S) : commutator ↥K = ⊤ := by
  have h1 : (commutator ↥K).map K.subtype = K := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact h.hK.2.1
  have h2 : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective K.subtype_injective (h1.trans h2.symm)

theorem K_le_of_normal_noncentral (h : Setup28 W K S) (hq : CFSG.IsQuasisimple ↥(bar W K))
    {M : Subgroup X} (hMK : M ≤ K) (hMn : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M) {p : X}
    (hpM : p ∈ M) (hpz : p ∉ zPre W K) : K ≤ M := by
  set M' : Subgroup ↥K := M.subgroupOf K with hM'
  haveI hM'n : M'.Normal :=
    (Subgroup.normal_subgroupOf_iff hMK).mpr fun m k hm hk => hMn k hk m hm
  have hperf := commutator_K h
  set N' : Subgroup ↥(bar W K) := M'.map (toBar W K) with hN'
  haveI : N'.Normal := Subgroup.Normal.map hM'n (toBar W K) toBar_surjective
  have hpK : p ∈ K := hMK hpM
  have hN'nc : ¬ N' ≤ Subgroup.center ↥(bar W K) := by
    intro hle
    apply hpz
    have hmem : toBar W K ⟨p, hpK⟩ ∈ N' :=
      Subgroup.mem_map_of_mem _ (by rw [hM', Subgroup.mem_subgroupOf]; exact hpM)
    exact (zPre_iff ⟨p, hpK⟩).mpr (hle hmem)
  have hN'top : N' = ⊤ := eq_top_of_quasisimple_normal hq.1.commutator_eq_top hq.2.1 N' hN'nc
  have hsup : M' ⊔ (toBar W K).ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, ← hN', hN'top, Subgroup.comap_top]
  have hR : IsPGroup 2 ↥(toBar W K).ker := by
    intro g
    have hgW : ((g : ↥K) : X) ∈ W := toBar_eq_one_iff.mp g.2
    obtain ⟨n, hn⟩ := h.hW ⟨(g : ↥K), hgW⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hM'top := eq_top_of_perfect_of_sup_pGroup hperf M' _ hsup hR
  intro k hk
  have hk' : (⟨k, hk⟩ : ↥K) ∈ M' := hM'top ▸ Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf).mp hk'

end Normal

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.InducedAux
