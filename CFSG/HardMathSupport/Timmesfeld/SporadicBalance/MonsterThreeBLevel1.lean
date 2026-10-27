module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBSylFact
public import CFSG.YGroups.Y443.Tri.Finiteness

public section

open scoped Pointwise

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open _root_.Timmesfeld.M3B (F3 Vec Mat mget mmul mone meq matOf LM sylWords sylMats sylInv
  sylEnum sylRoots tMats sylCheck conjData grpCheck conjCheck conjBFS keyMap lookupIdx)

section Datum

theorem card_QQ : Nat.card QQ = 3 ^ 13 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact tbCommData.card_eq

theorem QQ_le_ker : QQ.subgroupOf tbL ≤ rhoL.ker := by
  intro b hb
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [coe_rhoL, Units.val_one]
  exact tbCommData.actMat_of_mem (Subgroup.mem_subgroupOf.1 hb)

theorem card_tbL_eq : Nat.card tbL = Nat.card rhoL.ker * Nat.card rhoL.range := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

theorem three_pow_13_dvd_ker : 3 ^ 13 ∣ Nat.card rhoL.ker := by
  have := Subgroup.card_dvd_of_le QQ_le_ker
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QQ_le_tbL).toEquiv, card_QQ] at this

@[expose] noncomputable def sylS (h : SylFact) : Subgroup (GL (Fin 12) (ZMod 3)) := h.choose

theorem sylS_le_range (h : SylFact) : sylS h ≤ rhoL.range := h.choose_spec.1

theorem card_sylS (h : SylFact) : Nat.card (sylS h) = 3 ^ 7 := h.choose_spec.2.1

theorem sylS_conj (h : SylFact) : ∀ y ∈ sylS h, y ^ 3 = 1 → y ≠ 1 → ∃ g : tbL, ∃ j < 3,
    (((rhoL g)⁻¹ * y * rhoL g : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)) =
      toMatrix (tMats ())[j]! :=
  h.choose_spec.2.2

end Datum

section Orders

theorem card_tbL_dvd : Nat.card tbL ∣ CFSG.Open.monsterOrder := by
  rw [← CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
  exact Subgroup.card_subgroup_dvd_card tbL

theorem not_three_pow_21_dvd : ¬ 3 ^ 21 ∣ CFSG.Open.monsterOrder := by
  unfold CFSG.Open.monsterOrder
  decide

theorem not_three_pow_8_dvd_range : ¬ 3 ^ 8 ∣ Nat.card rhoL.range := by
  intro h
  apply not_three_pow_21_dvd
  have := Nat.mul_dvd_mul three_pow_13_dvd_ker h
  rw [← pow_add, ← card_tbL_eq] at this
  exact this.trans card_tbL_dvd

theorem three_pow_twenty_dvd (h : SylFact) : 3 ^ 20 ∣ Nat.card tbL := by
  have h7 : 3 ^ 7 ∣ Nat.card rhoL.range := by
    rw [← card_sylS h]
    exact Subgroup.card_dvd_of_le (sylS_le_range h)
  rw [card_tbL_eq, show 20 = 13 + 7 by norm_num, pow_add]
  exact Nat.mul_dvd_mul three_pow_13_dvd_ker h7

theorem exists_conj_mem_sylow_three' {H : Type*} [Group H] [Finite H] (P : Sylow 3 H) {s : H}
    (hs : orderOf s = 3) : ∃ g : H, g * s * g⁻¹ ∈ (P : Subgroup H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsP : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨R, hR⟩ := hsP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H R P
  refine ⟨g, ?_⟩
  have h1 : s ∈ (R : Subgroup H) := hR (Subgroup.mem_zpowers s)
  have h2 := Subgroup.smul_mem_pointwise_smul s (MulAut.conj g) (R : Subgroup H) h1
  have h3 : ((g • R : Sylow 3 H) : Subgroup H) = MulAut.conj g • (R : Subgroup H) := rfl
  rw [← h3, hg] at h2
  simpa [MulAut.smul_def] using h2

theorem factorization_range (h : SylFact) :
    (Nat.card rhoL.range).factorization 3 = 7 := by
  have hpos : Nat.card rhoL.range ≠ 0 := Nat.card_pos.ne'
  have h7 : 3 ^ 7 ∣ Nat.card rhoL.range := by
    rw [← card_sylS h]
    exact Subgroup.card_dvd_of_le (sylS_le_range h)
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).1 h7
  have hlt : ¬ 8 ≤ (Nat.card rhoL.range).factorization 3 := fun h8 =>
    not_three_pow_8_dvd_range ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).2 h8)
  omega

@[expose] noncomputable def sylP (h : SylFact) : Sylow 3 rhoL.range :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard ((sylS h).subgroupOf rhoL.range) (by
    rw [factorization_range h,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sylS_le_range h)).toEquiv, card_sylS h])

theorem exists_conj_tMats (hsyl : SylFact) {x : Gmat} (hx : x ∈ tbL)
    (hx3 : x ^ 3 = 1) (hρ : CommData.actMat 3 tbq tbw tbM x ≠ 1) :
    ∃ g ∈ tbL, ∃ j < 3,
      CommData.actMat 3 tbq tbw tbM (g⁻¹ * x * g) = toMatrix (tMats ())[j]! := by
  classical
  obtain ⟨y, hydef⟩ : ∃ y : rhoL.range, y = ⟨rhoL ⟨x, hx⟩, ⟨_, rfl⟩⟩ := ⟨_, rfl⟩
  have hy1 : y ≠ 1 := by
    intro h1
    apply hρ
    have := congrArg (fun z : rhoL.range => ((z : GL (Fin 12) (ZMod 3)) :
      Matrix (Fin 12) (Fin 12) (ZMod 3))) h1
    simpa [hydef, coe_rhoL] using this
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hydef, ← map_pow]
    have : (⟨x, hx⟩ : tbL) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hx3)
    rw [this, map_one]; rfl
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨k, hkP⟩ := exists_conj_mem_sylow_three' (sylP hsyl) hyo
  have hkS : ((k * y * k⁻¹ : rhoL.range) : GL (Fin 12) (ZMod 3)) ∈ sylS hsyl :=
    Subgroup.mem_subgroupOf.1 hkP
  have hky : ((k * y * k⁻¹ : rhoL.range) : GL (Fin 12) (ZMod 3)) =
      (k : GL (Fin 12) (ZMod 3)) * rhoL ⟨x, hx⟩ * (k : GL (Fin 12) (ZMod 3))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hydef]
  have hz3 : ((k * y * k⁻¹ : rhoL.range) : GL (Fin 12) (ZMod 3)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, conj_pow, hy3, mul_one, mul_inv_cancel, Subgroup.coe_one]
  have hz1 : ((k * y * k⁻¹ : rhoL.range) : GL (Fin 12) (ZMod 3)) ≠ 1 := by
    intro he
    apply hy1
    have : k * y * k⁻¹ = 1 := Subtype.ext he
    calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
      _ = 1 := by rw [this]; group
  obtain ⟨g', j, hj3, hconj⟩ := sylS_conj hsyl _ hkS hz3 hz1
  obtain ⟨a, ha⟩ := k.2
  refine ⟨((a⁻¹ * g' : tbL) : Gmat), (a⁻¹ * g').2, j, hj3, ?_⟩
  have hY : rhoL ((a⁻¹ * g')⁻¹ * ⟨x, hx⟩ * (a⁻¹ * g')) =
      (rhoL g')⁻¹ * ((k : GL (Fin 12) (ZMod 3)) * rhoL ⟨x, hx⟩ * (k : GL (Fin 12) (ZMod 3))⁻¹) *
        rhoL g' := by
    simp only [map_mul, map_inv, ha]
    group
  change ((rhoL ((a⁻¹ * g')⁻¹ * ⟨x, hx⟩ * (a⁻¹ * g')) : GL (Fin 12) (ZMod 3)) :
    Matrix (Fin 12) (Fin 12) (ZMod 3)) = _
  rw [hY, ← hky]
  exact hconj

end Orders

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
