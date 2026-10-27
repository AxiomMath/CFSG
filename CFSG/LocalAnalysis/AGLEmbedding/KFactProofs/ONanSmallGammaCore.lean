module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34LocalGroup

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallGamma

open CFSG.Open

section Normalizer

variable {G : Type*} [Group G]

theorem glbCore_le_of_normalizer_le [Finite G] {p : ℕ} (hp : 2 ≤ p) {T : Subgroup G}
    (h : ∀ Q : Subgroup G, Q ≤ T → Q ≠ ⊥ →
      Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (T : Set G)) :
    GLBCore p 1 T ≤ Subgroup.normalizer (T : Set G) := by
  unfold GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQT, hQ, rfl⟩
  exact h Q hQT (KFactProofs.L34Local.LocalData.ne_bot_of_one_le_pRank hp hQ)

theorem normalizer_le_of_centralizer_le {T Q : Subgroup G}
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hC : ∀ t ∈ T, t ≠ 1 → ∀ g : G, g * t = t * g → g ∈ T)
    (hQT : Q ≤ T) (hQ : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (T : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (Q : Set G), ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro g hg x hx
    obtain ⟨q, hq⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ
    have hq' : g * (q : G) * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hg q).1 q.2
    refine hC (g * q * g⁻¹) (hQT hq') ?_ _ ?_
    · intro h1
      apply hq
      have : (q : G) = 1 := by
        have h2 : g⁻¹ * (g * (q : G) * g⁻¹) * g = g⁻¹ * 1 * g := by rw [h1]
        simpa [mul_assoc] using h2
      exact Subtype.ext this
    · have hqT' : (q : G) ∈ T := hQT q.2
      have := hcomm x hx q hqT'
      calc g * x * g⁻¹ * (g * q * g⁻¹) = g * (x * q) * g⁻¹ := by group
        _ = g * (q * x) * g⁻¹ := by rw [this]
        _ = g * q * g⁻¹ * (g * x * g⁻¹) := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

end Normalizer

section Solvable

theorem isSolvable_of_pGroup_quotient {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (S : Subgroup H) [S.Normal] (hS : IsPGroup p S)
    (hQ : IsPGroup q (H ⧸ S)) : Group.IsSolvable H := by
  have := hS.isNilpotent
  have := hQ.isNilpotent
  exact Group.isSolvable_of_ker_le_range S.subtype (QuotientGroup.mk' S)
    (by simp [QuotientGroup.ker_mk'])

variable {G : Type*} [Group G] [Finite G]

theorem isSolvable_normalizer_of_card {T : Subgroup G} {a b : ℕ} (hT : Nat.card T = 3 ^ a)
    (hN : Nat.card (Subgroup.normalizer (T : Set G)) = 3 ^ a * 2 ^ b) :
    Group.IsSolvable (Subgroup.normalizer (T : Set G)) := by
  set N := Subgroup.normalizer (T : Set G) with hNdef
  have hTN : T ≤ N := Subgroup.le_normalizer
  let H : Subgroup N := T.subgroupOf N
  have hHcard : Nat.card H = 3 ^ a := by
    rw [← hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hidx : H.index = 2 ^ b := by
    have h1 := H.index_mul_card
    rw [hHcard, hN] at h1
    have h3 : 0 < 3 ^ a := by positivity
    exact Nat.eq_of_mul_eq_mul_right h3 (h1.trans (mul_comm _ _))
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSolvable_of_pGroup_quotient (p := 3) (q := 2) H (IsPGroup.of_card hHcard)
    (IsPGroup.of_card (n := b) (show Nat.card (N ⧸ H) = 2 ^ b from hidx))

end Solvable

theorem exists_equiv_map_eq {L G : Type*} [Group L] [Finite L] [Group G] {p : ℕ} [Fact p.Prime]
    (e : L ≃* G) (U : Sylow p L) (P : Sylow p G) :
    ∃ e' : L ≃* G, (U : Subgroup L).map e'.toMonoidHom = P := by
  have : Finite G := Finite.of_equiv L e.toEquiv
  set U' := U.mapSurjective (f := (e : L →* G)) e.surjective with hU'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U' P
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have h2 : ((g • U' : Sylow p G) : Subgroup G) =
      (U' : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  rw [hg, hU', Sylow.coe_mapSurjective, Subgroup.map_map] at h2
  exact h2.symm

structure SmallGammaData (G : Type*) [Group G] (T : Subgroup G) : Prop where
  normalizer_le : ∀ Q : Subgroup G, Q ≤ T → Q ≠ ⊥ →
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (T : Set G)
  solvable : Group.IsSolvable (Subgroup.normalizer (T : Set G))

namespace SmallGammaData

section Map

variable {G G' : Type*} [Group G] [Group G'] {T : Subgroup G} {T' : Subgroup G'}

theorem mem_normalizer_iff (e : G ≃* G') (hT : ∀ g, g ∈ T ↔ e g ∈ T') (n : G) :
    n ∈ Subgroup.normalizer (T : Set G) ↔ e n ∈ Subgroup.normalizer (T' : Set G') := by
  have hT' : ∀ y, y ∈ T' ↔ e.symm y ∈ T := fun y => by simpa using (hT (e.symm y)).symm
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hn y
    rw [hT' y, hT' (e n * y * (e n)⁻¹)]
    simpa using hn (e.symm y)
  · intro hn x
    have h1 := hn (e x)
    have e1 : e n * e x * (e n)⁻¹ = e (n * x * n⁻¹) := by simp
    rw [e1, ← hT, ← hT] at h1
    exact h1

theorem map (e : G ≃* G') (hT : ∀ g, g ∈ T ↔ e g ∈ T') (h : SmallGammaData G T) :
    SmallGammaData G' T' := by
  have hT' : ∀ y, y ∈ T' ↔ e.symm y ∈ T := fun y => by simpa using (hT (e.symm y)).symm
  refine ⟨fun Q' hQ'T hQ' y' hy' => ?_, ?_⟩
  · set Q : Subgroup G := Q'.comap e.toMonoidHom with hQdef
    have hQmem : ∀ g, g ∈ Q ↔ e g ∈ Q' := fun g => Iff.rfl
    have hQT : Q ≤ T := fun g hg => (hT g).2 (hQ'T hg)
    have hQbot : Q ≠ ⊥ := by
      intro hbot
      apply hQ'
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxQ : e.symm x ∈ Q := by rw [hQmem]; simpa using hx
      rw [hbot, Subgroup.mem_bot] at hxQ
      simpa using congrArg e hxQ
    have hnorm : ∀ n : G, n ∈ Subgroup.normalizer (Q : Set G) ↔
        e n ∈ Subgroup.normalizer (Q' : Set G') := fun n =>
      mem_normalizer_iff (T := Q) (T' := Q') e hQmem n
    have hy := (hnorm (e.symm y')).2 (by simpa using hy')
    have := (mem_normalizer_iff (T := T) (T' := T') e hT _).1 (h.normalizer_le Q hQT hQbot hy)
    simpa using this
  · let f : Subgroup.normalizer (T : Set G) ≃* Subgroup.normalizer (T' : Set G') :=
      { toFun := fun x => ⟨e x, (mem_normalizer_iff e hT x).1 x.2⟩
        invFun := fun y => ⟨e.symm y, (mem_normalizer_iff e hT _).2 (by simp)⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp) }
    have := h.solvable
    exact Group.isSolvable_of_isSolvable_injective (f := f.symm.toMonoidHom) f.symm.injective

theorem of_equiv_map (e : G ≃* G') (hT : T.map e.toMonoidHom = T') (h : SmallGammaData G' T') :
    SmallGammaData G T :=
  map e.symm (fun y => by rw [← hT, Subgroup.mem_map_equiv]) h

end Map

theorem isSolvable_glbCore {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (h : SmallGammaData G T) : Group.IsSolvable (GLBCore 3 1 T) := by
  have hle : GLBCore 3 1 T ≤ Subgroup.normalizer (T : Set G) :=
    glbCore_le_of_normalizer_le (by norm_num) h.normalizer_le
  have := h.solvable
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem of_centralizer {G : Type*} [Group G] [Finite G] {T : Subgroup G} {a b : ℕ}
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hC : ∀ t ∈ T, t ≠ 1 → ∀ g : G, g * t = t * g → g ∈ T) (hT : Nat.card T = 3 ^ a)
    (hN : Nat.card (Subgroup.normalizer (T : Set G)) = 3 ^ a * 2 ^ b) : SmallGammaData G T :=
  ⟨fun _ hQT hQ => normalizer_le_of_centralizer_le hcomm hC hQT hQ,
    isSolvable_normalizer_of_card hT hN⟩

theorem of_localData {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (h : KFactProofs.L34Local.LocalData G T) : SmallGammaData G T :=
  of_centralizer (a := 2) (b := 3) (KFactProofs.L34Local.LocalData.commute_of_card_eq h)
    h.centralizer_le (by rw [h.card_eq]; norm_num) (by rw [h.card_normalizer]; norm_num)

end SmallGammaData

end CFSG.AGLEmbedding.KFactProofs.SmallGamma
