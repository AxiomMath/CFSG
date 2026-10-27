module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Bridge

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Act

variable {G : Type} [Group G] [Finite G]

open Classical in
@[expose] noncomputable def actS (K S : Subgroup G) (hS : S ≤ Subgroup.normalizer (K : Set G)) :
    G → ↥(autOn S K) := fun g =>
  if hg : g ∈ S then
    ⟨conjAct K ⟨g, hS hg⟩, Subgroup.mem_map.mpr
      ⟨⟨g, hS hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩⟩
  else 1

omit [Finite G] in
theorem actS_of_mem {K S : Subgroup G} (hS : S ≤ Subgroup.normalizer (K : Set G)) {g : G}
    (hg : g ∈ S) :
    actS K S hS g = ⟨conjAct K ⟨g, hS hg⟩, Subgroup.mem_map.mpr
      ⟨⟨g, hS hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩⟩ := by
  simp [actS, hg]

omit [Finite G] in
theorem actS_apply {K S : Subgroup G} (hS : S ≤ Subgroup.normalizer (K : Set G)) {g : G}
    (hg : g ∈ S) (k : ↥K) :
    ((((actS K S hS g : ↥(autOn S K)) : MulAut ↥K) k : ↥K) : G) = g * k * g⁻¹ := by
  rw [actS_of_mem hS hg]
  rfl

theorem sBar_actS {K S A : Subgroup G} (hS : S ≤ Subgroup.normalizer (K : Set G))
    (hA : ∀ s ∈ S, s ∈ A ↔ ∀ k ∈ K, s * k = k * s) {R : Subgroup ↥(autOn S K)}
    (hR : DS.DSData R) : SBar S A (actS K S hS) R where
  mul := by
    intro a ha b hb
    have hab : a * b ∈ S := S.mul_mem ha hb
    apply Subtype.ext
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    show ((((actS K S hS (a * b) : ↥(autOn S K)) : MulAut ↥K) k : ↥K) : G) = _
    rw [actS_apply hS hab]
    show _ = ((((actS K S hS a : ↥(autOn S K)) : MulAut ↥K)
      ((((actS K S hS b : ↥(autOn S K)) : MulAut ↥K) k : ↥K)) : ↥K) : G)
    rw [actS_apply hS ha, actS_apply hS hb]
    group
  surj := by
    rintro ⟨p, hp⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hp
    have hxS : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
    refine ⟨(x : G), hxS, ?_⟩
    rw [actS_of_mem hS hxS]
  ker := by
    intro s hs
    rw [hA s hs]
    constructor
    · intro h1 k hk
      have h2 := congrArg (fun φ : ↥(autOn S K) => (((φ : MulAut ↥K) ⟨k, hk⟩ : ↥K) : G)) h1
      rw [actS_apply hS hs] at h2
      have h3 : s * k * s⁻¹ = k := h2
      calc s * k = s * k * s⁻¹ * s := by group
        _ = k * s := by rw [h3]
    · intro h1
      apply Subtype.ext
      apply MulEquiv.ext
      intro k
      apply Subtype.ext
      show ((((actS K S hS s : ↥(autOn S K)) : MulAut ↥K) k : ↥K) : G) = k
      rw [actS_apply hS hs]
      calc s * (k : G) * s⁻¹ = (k : G) * s * s⁻¹ := by rw [h1 k k.2]
        _ = k := by group
  ds := hR

end Act

section Shape

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem Lv2520.S_le_normalizer (h : Lv2520 N t zK) : N.S ≤ Subgroup.normalizer (N.K : Set G) :=
  N.S_le_normalizer_K h.hKH

theorem Lv2520.sBar (h : Lv2520 N t zK) {R : Subgroup ↥(autOn N.S N.K)} (hR : DS.DSData R) :
    SBar N.S N.SC (actS N.K N.S h.S_le_normalizer) R :=
  sBar_actS h.S_le_normalizer
    (fun _ hs' => ⟨fun hc => h.SC_commutes hc, fun hc =>
      h.mem_SC_of_commutes (N.S_le_H hs') hc⟩) hR

theorem Lv2520.SK_normal_in_S (h : Lv2520 N t zK) {s : G} (hs' : s ∈ N.S) {q : G}
    (hq : q ∈ N.SK) : s * q * s⁻¹ ∈ N.SK := by
  refine ⟨N.S.mul_mem (N.S.mul_mem hs' hq.1) (N.S.inv_mem hs'), ?_⟩
  have hsN : s ∈ Subgroup.normalizer (N.K : Set G) := h.S_le_normalizer hs'
  exact (Subgroup.mem_normalizer_iff.mp hsN q).mp hq.2

end Shape

end CFSG.QuasithinUnique
