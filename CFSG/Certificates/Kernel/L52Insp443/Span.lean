module

public import CFSG.Certificates.Kernel.L52Insp443.Act
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermKit

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem listBeq_iff : ∀ (L M : List ℕ), listBeq L M = true ↔ L = M
  | [], [] => by simp [listBeq]
  | [], _ :: _ => by simp [listBeq]
  | _ :: _, [] => by simp [listBeq]
  | x :: L, y :: M => by
    change CFSG.KC.Ord.andB (Nat.beq x y) (listBeq L M) = true ↔ _
    rw [andB_true, listBeq_iff L M, Nat.beq_eq, List.cons.injEq]

theorem nodupK_iff : ∀ L : List ℕ, nodupK L = true ↔ L.Nodup
  | [] => by simp [nodupK]
  | x :: L => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (memK x L)) (nodupK L) = true ↔ _
    rw [andB_true, notB_true, nodupK_iff L, List.nodup_cons, ← memK_iff, Bool.not_eq_true]

theorem mapMulK_eq (b : ℕ) : ∀ S : List ℕ, mapMulK b S = S.map (mmulK b)
  | [] => rfl
  | s :: S => by
    change mmulK b s :: mapMulK b S = _
    rw [mapMulK_eq b S, List.map_cons]

theorem spanK_cons (b : ℕ) (bs : List ℕ) :
    spanK (b :: bs) = spanK bs ++ (spanK bs).map (mmulK b) := by
  change List.append (spanK bs) (mapMulK b (spanK bs)) = _
  rw [mapMulK_eq]
  rfl

theorem spanK_nil : spanK [] = [idK] := rfl

theorem length_spanK : ∀ bs : List ℕ, (spanK bs).length = 2 ^ bs.length
  | [] => rfl
  | b :: bs => by
    rw [spanK_cons, List.length_append, List.length_map, length_spanK bs, List.length_cons,
      pow_succ]
    omega

theorem commK_iff (a b : ℕ) : commK a b = true ↔ mmulK a b = mmulK b a := by
  unfold commK
  rw [Nat.beq_eq]

section Abstract

variable {Γ : Type*} [Group Γ] (κ : Γ → ℕ) (hone : κ 1 = idK)
  (hmul : ∀ g h : Γ, κ (g * h) = mmulK (κ g) (κ h)) (hinj : Function.Injective κ) (f : ℕ → Γ)

include hone hmul in
theorem exists_of_mem_spanK {n : ℕ} (hn : n < 2 ^ 32) (φ : Γ →* Equiv.Perm (Fin n)) :
    ∀ {bs : List ℕ} {Ts : List Table}, (∀ b ∈ bs, κ (f b) = b) →
      List.Forall₂ (Rep n) Ts (bs.map fun b => φ (f b)) → ∀ c ∈ spanK bs,
        ∃ x : Γ, κ x = c ∧ ∃ mask < 2 ^ Ts.length, Rep n (maskProd n Ts mask) (φ x)
  | [], [], _, _, c, hc => by
    rw [spanK_nil, List.mem_singleton] at hc
    refine ⟨1, by rw [hone, hc], 0, by norm_num, ?_⟩
    rw [map_one]
    exact Rep.idT hn
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | b :: bs, T :: Ts, hf, h, c, hc => by
    rw [List.map_cons, List.forall₂_cons] at h
    obtain ⟨hT, hTs⟩ := h
    have hb : κ (f b) = b := hf b List.mem_cons_self
    have ih := exists_of_mem_spanK hn φ (bs := bs) (Ts := Ts)
      (fun d hd => hf d (List.mem_cons_of_mem b hd)) hTs
    rw [spanK_cons, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨x, hx, m, hm, hr⟩ := ih c hc
      refine ⟨x, hx, 2 * m, by rw [List.length_cons, pow_succ]; omega, ?_⟩
      have e : maskProd n (T :: Ts) (2 * m) = compT n (idT n) (maskProd n Ts m) := by
        rw [maskProd, if_neg (by omega), Nat.mul_div_cancel_left m (by norm_num)]
      rw [e, ← one_mul (φ x)]
      exact Rep.compT (Rep.idT hn) hr
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      obtain ⟨y, hy, m, hm, hr⟩ := ih s hs
      refine ⟨f b * y, by rw [hmul, hb, hy], 2 * m + 1,
        by rw [List.length_cons, pow_succ]; omega, ?_⟩
      have e : maskProd n (T :: Ts) (2 * m + 1) = compT n T (maskProd n Ts m) := by
        rw [maskProd, if_pos (by omega), show (2 * m + 1) / 2 = m by omega]
      rw [e, map_mul]
      exact Rep.compT hT hr

include hone hmul hinj in
theorem inSp_of_mem_spanK {n : ℕ} (hn : n < 2 ^ 32) (φ : Γ →* Equiv.Perm (Fin n))
    {bs : List ℕ} {Ts : List Table} (hf : ∀ b ∈ bs, κ (f b) = b)
    (h : List.Forall₂ (Rep n) Ts (bs.map fun b => φ (f b))) {x : Γ} (hx : κ x ∈ spanK bs)
    {T : Table} (hT : Rep n T (φ x)) : inSp n (spanTabs n Ts) T = true := by
  obtain ⟨y, hy, m, hm, hr⟩ := exists_of_mem_spanK κ hone hmul f hn φ hf h _ hx
  rw [hinj hy] at hr
  unfold inSp spanTabs
  rw [List.any_eq_true]
  exact ⟨maskProd n Ts m, List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩,
    (tblEq_iff_eq hr hT).mpr rfl⟩

include hmul hinj in
theorem mem_of_comm_card [Finite Γ] {bs S : List ℕ} (hf : ∀ b ∈ bs, κ (f b) = b)
    (hS : ∀ s ∈ S, ∃ g : Γ, κ g = s) (hnd : S.Nodup)
    (hc : ∀ s ∈ S, ∀ b ∈ bs, mmulK s b = mmulK b s)
    (hcard : Nat.card {g : Γ // ∀ b ∈ bs, g * f b = f b * g} = S.length)
    {g : Γ} (hg : ∀ b ∈ bs, g * f b = f b * g) : κ g ∈ S := by
  have hsub : {x : Γ | κ x ∈ S} ⊆ {x : Γ | ∀ b ∈ bs, x * f b = f b * x} := fun x hx b hb => by
    apply hinj
    rw [hmul, hmul, hf b hb]
    exact hc _ hx b hb
  have himg : κ '' {x : Γ | κ x ∈ S} = (S.toFinset : Set ℕ) := by
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq, List.coe_toFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hs
      obtain ⟨x, hx⟩ := hS s hs
      exact ⟨x, hx ▸ hs, hx⟩
  have hA : ({x : Γ | κ x ∈ S} : Set Γ).ncard = S.length := by
    rw [← Set.ncard_image_of_injective _ hinj, himg, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hnd]
  have hB : ({x : Γ | ∀ b ∈ bs, x * f b = f b * x} : Set Γ).ncard = S.length := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hA, hB]) (Set.toFinite _)
  have hg' : g ∈ ({x : Γ | ∀ b ∈ bs, x * f b = f b * x} : Set Γ) := hg
  rw [← heq] at hg'
  exact hg'

end Abstract

theorem comm_of_commAllT {n : ℕ} {T : Table} {x : Equiv.Perm (Fin n)} (hT : Rep n T x) :
    ∀ {Ts : List Table} {xs : List (Equiv.Perm (Fin n))}, List.Forall₂ (Rep n) Ts xs →
      commAllT n Ts T = true → ∀ y ∈ xs, x * y = y * x
  | [], [], .nil, _ => by simp
  | U :: Ts, y :: xs, .cons hU hTs, h => by
    unfold commAllT at h
    rw [List.all_cons, Bool.and_eq_true] at h
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact (CFSG.SectionRank.QTK.Insp443.PermKit.commT2_iff hT hU).mp h.1
    · exact comm_of_commAllT hT hTs h.2 z hz

end CFSG.KC.L52I

end
