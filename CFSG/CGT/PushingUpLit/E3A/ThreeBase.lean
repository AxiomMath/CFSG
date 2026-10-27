module

public import CFSG.RankThree.PartOne.SolD3.Struct

public section

namespace CFSG.CGT.PushingUpLit.E3A

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit.SolK CFSG.RankThree.PartOne.SolD3
open CFSG.Assembly (pCoreOf)

theorem le_sylow_of_le_normalizer {G : Type*} [Group G] (S : Sylow 2 G) {K : Subgroup G}
    (hK : IsPGroup 2 K) (h : K ≤ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    K ≤ (S : Subgroup G) :=
  le_sup_left.trans (S.is_maximal' (hK.to_sup_of_normal_right' S.isPGroup' h) le_sup_right).le

theorem le_sylow_of_normalizes {G : Type*} [Group G] (S : Sylow 2 G) {K : Subgroup G}
    (hK : IsPGroup 2 K) (h : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G)) :
    K ≤ (S : Subgroup G) :=
  le_sup_right.trans (S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' hK h) le_sup_left).le

theorem exists_central_of_normalizes {G : Type*} [Group G] [Finite G] {S K : Subgroup G}
    (hS : IsPGroup 2 S)
    (hKS : K ≤ S) (hK1 : K ≠ ⊥) (hSN : S ≤ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, k ≠ 1 ∧ ∀ s ∈ S, k * s = s * k := by
  have hnorm : (K.subgroupOf S).Normal :=
    ⟨fun x hx g => (Subgroup.mem_normalizer_iff.1 (hSN g.2) x).1 hx⟩
  have hne : K.subgroupOf S ≠ ⊥ := by
    intro h
    apply hK1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hKS hx⟩ : S) ∈ K.subgroupOf S := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  have : Group.IsNilpotent S := hS.isNilpotent
  obtain ⟨⟨u, huK, huZ⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  exact ⟨u, huK, fun h => hu1 (Subtype.ext (Subtype.ext h)), fun s hs =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 huZ ⟨s, hs⟩)).symm⟩

@[expose] def SylowCenterTwo (G : Type*) [Group G] : Prop :=
  ∀ S : Sylow 2 G, ∀ u v : G, u ∈ (S : Subgroup G) → v ∈ (S : Subgroup G) →
    (∀ s ∈ (S : Subgroup G), u * s = s * u) → (∀ s ∈ (S : Subgroup G), v * s = s * v) →
    u = 1 ∨ v = 1 ∨ u = v

theorem SylowCenterTwo.of_one {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : ∀ u v : G, u ∈ (S : Subgroup G) → v ∈ (S : Subgroup G) →
      (∀ s ∈ (S : Subgroup G), u * s = s * u) → (∀ s ∈ (S : Subgroup G), v * s = s * v) →
      u = 1 ∨ v = 1 ∨ u = v) : SylowCenterTwo G := by
  intro Q u v hu hv hcu hcv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have hmap : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = (Q : Subgroup G) := by
    change (g • S : Sylow 2 G).toSubgroup = Q.toSubgroup
    rw [hg]
  have hmem : ∀ x : G, x ∈ (Q : Subgroup G) ↔ g⁻¹ * x * g ∈ (S : Subgroup G) := by
    intro x
    rw [← hmap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hcent : ∀ w : G, w ∈ (Q : Subgroup G) → (∀ s ∈ (Q : Subgroup G), w * s = s * w) →
      ∀ s ∈ (S : Subgroup G), (g⁻¹ * w * g) * s = s * (g⁻¹ * w * g) := by
    intro w hw hcw s hs
    have hs' : g * s * g⁻¹ ∈ (Q : Subgroup G) := (hmem _).2 (by simpa [mul_assoc] using hs)
    have := hcw _ hs'
    calc g⁻¹ * w * g * s = g⁻¹ * (w * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * w) * g := by rw [this]
      _ = s * (g⁻¹ * w * g) := by group
  have key := h (g⁻¹ * u * g) (g⁻¹ * v * g) ((hmem _).1 hu) ((hmem _).1 hv)
    (hcent u hu hcu) (hcent v hv hcv)
  have hinj : ∀ x y : G, g⁻¹ * x * g = g⁻¹ * y * g → x = y := fun x y hxy => by
    have := congrArg (fun z => g * z * g⁻¹) hxy
    simpa [mul_assoc] using this
  rcases key with h1 | h1 | h1
  · exact Or.inl (hinj u 1 (by simpa using h1))
  · exact Or.inr (Or.inl (hinj v 1 (by simpa using h1)))
  · exact Or.inr (Or.inr (hinj u v h1))

theorem SylowCenterTwo.map_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (hG : SylowCenterTwo G) (e : G ≃* H) : SylowCenterTwo H := by
  intro Q u v hu hv hcu hcv
  let S := Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hmap : (S : Subgroup G).map e.toMonoidHom = (Q : Subgroup H) := by
    simp [S, Subgroup.map_map]
  have hmem : ∀ x : G, x ∈ (S : Subgroup G) ↔ e x ∈ (Q : Subgroup H) := by
    intro x
    rw [← hmap]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← e.injective hyx]
  have hcent : ∀ w : H, w ∈ (Q : Subgroup H) → (∀ s ∈ (Q : Subgroup H), w * s = s * w) →
      ∀ s ∈ (S : Subgroup G), e.symm w * s = s * e.symm w := by
    intro w hw hcw s hs
    have := hcw (e s) ((hmem s).1 hs)
    apply e.injective
    simpa using this
  have key := hG S (e.symm u) (e.symm v) ((hmem _).2 (by simpa using hu))
    ((hmem _).2 (by simpa using hv)) (hcent u hu hcu) (hcent v hv hcv)
  rcases key with h1 | h1 | h1
  · exact Or.inl (by simpa using congrArg e h1)
  · exact Or.inr (Or.inl (by simpa using congrArg e h1))
  · exact Or.inr (Or.inr (e.symm.injective h1))

section Block

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem W_inf_R_eq_one {R X : Subgroup G} {a : G} (hb : Blk3 X a)
    (hXC : X ≤ Subgroup.centralizer (R : Set G)) {w : G} (hw : w ∈ pCoreOf 2 X) (hwR : w ∈ R) :
    w = 1 := by
  refine hb.fix w hw ?_
  have h := Subgroup.mem_centralizer_iff.1 (hXC hb.mem) w hwR
  rw [← h]
  group

omit [Finite G] in
theorem false_of_W_le_R {R X : Subgroup G} {a : G} (hb : Blk3 X a)
    (hXC : X ≤ Subgroup.centralizer (R : Set G)) (hW : pCoreOf 2 X ≤ R) : False := by
  obtain ⟨w, hw, hw1⟩ := hb.exists_ne_one
  exact hw1 (W_inf_R_eq_one hb hXC hw (hW hw))

theorem W_le_center_sylow {M X : Subgroup G} {a : G} (h : Hyp3 G M X) (hb : Blk3 X a)
    (S : Sylow 2 G) (hM : M = Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    ∀ w ∈ pCoreOf 2 X, w ∈ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), s * w * s⁻¹ = w := by
  have hWM : pCoreOf 2 X ≤ M := h.W_le_Q.trans (pCoreOf_le_self M)
  have hWS : pCoreOf 2 X ≤ (S : Subgroup G) :=
    le_sylow_of_le_normalizer S (isPGroup_pCoreOf' X) (by rw [← hM]; exact hWM)
  have hSM : (S : Subgroup G) ≤ M := by
    rw [hM]
    exact Subgroup.le_normalizer
  have hSQ : (S : Subgroup G) ≤ pCoreOf 2 M := by
    refine le_pCoreOf_of_normalized hSM (fun m hm x hx => ?_) S.isPGroup'
    rw [hM] at hm
    exact (Subgroup.mem_normalizer_iff.1 hm x).1 hx
  intro w hw
  exact ⟨hWS hw, fun s hs => h.q_comm_W hb (hSQ hs) w hw⟩

theorem false_of_sylowCenterTwo {R X : Subgroup G} {a : G}
    (h : Hyp3 G (Subgroup.normalizer (R : Set G)) X) (hb : Blk3 X a)
    (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hSR : ∀ S : Sylow 2 G, R ≤ (S : Subgroup G) →
      (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G))
    (hXC : X ≤ Subgroup.centralizer (R : Set G)) (hZ : SylowCenterTwo G) : False := by
  obtain ⟨S, hRS⟩ := hR2.exists_le_sylow
  have hSM := hSR S hRS
  have hSW : (S : Subgroup G) ≤ Subgroup.normalizer ((pCoreOf 2 X : Subgroup G) : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => h.W_normalized (hSM hs) hw, fun hw => ?_⟩
    have := h.W_normalized ((Subgroup.normalizer (R : Set G)).inv_mem (hSM hs)) hw
    simpa [mul_assoc] using this
  have hWS : pCoreOf 2 X ≤ (S : Subgroup G) := le_sylow_of_normalizes S (isPGroup_pCoreOf' X) hSW
  obtain ⟨u, huW, hu1, huc⟩ := exists_central_of_normalizes S.isPGroup' hWS hb.W_ne_bot hSW
  obtain ⟨v, hvR, hv1, hvc⟩ := exists_central_of_normalizes S.isPGroup' hRS hR1 hSM
  rcases hZ S u v (hWS huW) (hRS hvR) huc hvc with h1 | h1 | h1
  · exact hu1 h1
  · exact hv1 h1
  · exact hu1 (W_inf_R_eq_one hb hXC huW (h1 ▸ hvR))

end Block

end CFSG.CGT.PushingUpLit.E3A
