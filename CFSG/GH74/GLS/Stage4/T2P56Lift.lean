module

public import CFSG.GH74.GLS.Stage4.T2P56Transfer
public import CFSG.GH74.Uniqueness.Section161
public import CFSG.GH74.GLS.Stage4.T2FourQ
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.LU.Local.L3Facts
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise MatrixGroups

section Core

variable {Y : Type} [Group Y] (N : Subgroup Y) [N.Normal] (E : Subgroup (Y ⧸ N))

theorem ker_le_comap : N ≤ E.comap (QuotientGroup.mk' N) := by
  intro n hn
  rw [Subgroup.mem_comap]
  have : QuotientGroup.mk' N n = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hn
  rw [this]; exact E.one_mem

theorem map_sup_ker (P : Subgroup Y) : (P ⊔ N).map (QuotientGroup.mk' N) = P.map (QuotientGroup.mk' N) := by
  rw [Subgroup.map_sup]
  have : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [this, sup_bot_eq]

theorem exists_perfect_core [Finite Y] [E.Normal] (hE : ⁅E, E⁆ = E) :
    ∃ P : Subgroup Y, P.Normal ∧ P ≤ E.comap (QuotientGroup.mk' N) ∧
      P ⊔ N = E.comap (QuotientGroup.mk' N) ∧ ⁅P, P⁆ = P := by
  classical
  set π := QuotientGroup.mk' N with hπ
  have hker : N ≤ E.comap π := ker_le_comap N E
  have hEn : (E.comap π).Normal := Subgroup.Normal.comap inferInstance π
  let S : Set (Subgroup Y) := {P | P.Normal ∧ P ≤ E.comap π ∧ P ⊔ N = E.comap π}
  have hS : E.comap π ∈ S := ⟨hEn, le_rfl, sup_eq_left.2 hker⟩
  obtain ⟨P, ⟨hPn, hPle, hPsup⟩, hPmin⟩ := (wellFounded_lt (α := Subgroup Y)).has_min S ⟨_, hS⟩
  refine ⟨P, hPn, hPle, hPsup, ?_⟩
  have hmapP : P.map π = E := by
    have h1 : (P ⊔ N).map π = E := by
      rw [hPsup]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) E
    rw [map_sup_ker N] at h1
    exact h1
  have hP'le : ⁅P, P⁆ ≤ P := Subgroup.commutator_le_self P
  have hP'n : (⁅P, P⁆ : Subgroup Y).Normal := Subgroup.commutator_normal P P
  have hP'sup : ⁅P, P⁆ ⊔ N = E.comap π := by
    have hmap' : (⁅P, P⁆ : Subgroup Y).map π = E := by
      rw [Subgroup.map_commutator, hmapP]; exact hE
    have hNle : N ≤ ⁅P, P⁆ ⊔ N := le_sup_right
    have h2 : ((⁅P, P⁆ ⊔ N : Subgroup Y)).map π = E := by
      rw [map_sup_ker N]; exact hmap'
    have h3 : (⁅P, P⁆ ⊔ N : Subgroup Y) = ((⁅P, P⁆ ⊔ N : Subgroup Y).map π).comap π := by
      rw [Subgroup.comap_map_eq_self]
      rw [hπ, QuotientGroup.ker_mk']
      exact hNle
    rw [h3, h2]
  have hnotlt := hPmin ⁅P, P⁆ ⟨hP'n, hP'le.trans hPle, hP'sup⟩
  refine le_antisymm hP'le ?_
  by_contra hnle
  exact hnotlt (lt_of_le_not_ge hP'le hnle)

theorem perfect_eq_bot_of_solvable {Z : Type*} [Group Z] {M : Subgroup Z} (hperf : ⁅M, M⁆ = M)
    [Group.IsSolvable M] : M = ⊥ := by
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hperf
  by_contra h
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 h
  exact Group.IsPerfect.not_isSolvable M ‹_›

theorem map_eq_of_sup {P : Subgroup Y} (hPsup : P ⊔ N = E.comap (QuotientGroup.mk' N)) :
    P.map (QuotientGroup.mk' N) = E := by
  have h1 : (P ⊔ N).map (QuotientGroup.mk' N) = E := by
    rw [hPsup]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) E
  rw [map_sup_ker N] at h1
  exact h1

theorem perfect_le_core [Finite Y] (hNodd : Odd (Nat.card N)) {P : Subgroup Y} [P.Normal]
    (hPsup : P ⊔ N = E.comap (QuotientGroup.mk' N)) {K : Subgroup Y} (hK : ⁅K, K⁆ = K)
    (hKE : K.map (QuotientGroup.mk' N) ≤ E) : K ≤ P := by
  have hNsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  set ρ := QuotientGroup.mk' P with hρ
  have h1 : K.map ρ ≤ N.map ρ := by
    rintro _ ⟨k, hk, rfl⟩
    have hkE : k ∈ E.comap (QuotientGroup.mk' N) := hKE ⟨k, hk, rfl⟩
    rw [← hPsup] at hkE
    have hmul := Subgroup.normal_mul P N
    have hkE' : k ∈ ((P : Set Y) * (N : Set Y)) := by rw [← hmul]; exact hkE
    obtain ⟨p, hp, n, hn, rfl⟩ := hkE'
    refine ⟨n, hn, ?_⟩
    have hp1 : ρ p = 1 := by
      rw [hρ, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hp
    simp only [map_mul, hp1, one_mul]
  have hperf : Group.IsPerfect K := Subgroup.isPerfect_iff.2 hK
  have hMperf : ⁅K.map ρ, K.map ρ⁆ = K.map ρ := by
    rw [← Subgroup.map_commutator, hK]
  have hSsolv : Group.IsSolvable (N.map ρ) :=
    Group.isSolvable_of_surjective (f := ρ.subgroupMap N) (ρ.subgroupMap_surjective N)
  have hMsolv : Group.IsSolvable (K.map ρ) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h1)
  have hbot : K.map ρ = ⊥ := perfect_eq_bot_of_solvable hMperf
  intro k hk
  have : ρ k ∈ K.map ρ := ⟨k, hk, rfl⟩
  rw [hbot, Subgroup.mem_bot, hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  exact this

theorem maximal_normal_of_simple [E.Normal] (hEs : IsSimpleGroup E) {P : Subgroup Y}
    (hPmap : P.map (QuotientGroup.mk' N) = E) (M' : Subgroup Y) (hM'P : M' ≤ P)
    (hM'n : ∀ g ∈ P, ∀ m ∈ M', g * m * g⁻¹ ∈ M') (hBM : P ⊓ N ≤ M') : M' = P ⊓ N ∨ M' = P := by
  set π := QuotientGroup.mk' N with hπ
  let H' : Subgroup ↥E := (M'.map π).subgroupOf E
  have hH'n : H'.Normal := by
    refine ⟨fun m hm e => ?_⟩
    obtain ⟨x, hx, hxm⟩ := (Subgroup.mem_subgroupOf.1 hm)
    obtain ⟨p, hp, hpe⟩ : (e : Y ⧸ N) ∈ P.map π := by rw [hPmap]; exact e.2
    rw [Subgroup.mem_subgroupOf]
    refine ⟨p * x * p⁻¹, hM'n p hp x hx, ?_⟩
    simp only [map_mul, map_inv, hxm, hpe]
    rfl
  have := hH'n
  rcases hEs.eq_bot_or_eq_top_of_normal H' with h | h
  · left
    refine le_antisymm (fun x hx => ⟨hM'P hx, ?_⟩) hBM
    have hxE : π x ∈ E := by
      rw [← hPmap]; exact ⟨x, hM'P hx, rfl⟩
    have : (⟨π x, hxE⟩ : ↥E) ∈ H' := by
      rw [Subgroup.mem_subgroupOf]; exact ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    have h1 : π x = 1 := congrArg Subtype.val this
    exact (QuotientGroup.eq_one_iff x).1 h1
  · right
    refine le_antisymm hM'P (fun p hp => ?_)
    have hpE : π p ∈ E := by rw [← hPmap]; exact ⟨p, hp, rfl⟩
    have : (⟨π p, hpE⟩ : ↥E) ∈ H' := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨x, hx, hxp⟩ := Subgroup.mem_subgroupOf.1 this
    have hxN : x⁻¹ * p ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv]
      have : π x = π p := hxp
      rw [this]; exact inv_mul_cancel _
    have hxP : x⁻¹ * p ∈ P := P.mul_mem (P.inv_mem (hM'P hx)) hp
    have : x⁻¹ * p ∈ M' := hBM ⟨hxP, hxN⟩
    have h3 : p = x * (x⁻¹ * p) := by group
    rw [h3]
    exact M'.mul_mem hx this

end Core

section Star

variable {Y : Type} [Group Y]

theorem mem_normalizer_of_normal (B : Subgroup Y) [B.Normal] (g : Y) :
    g ∈ Subgroup.normalizer (B : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact Subgroup.Normal.conj_mem inferInstance h hh g
  · intro hh
    have := Subgroup.Normal.conj_mem inferInstance _ hh g⁻¹
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

theorem star_transfer {B : Subgroup Y} [B.Normal] {a e f : Y}
    (h : ∀ b ∈ B, b * e = e * b → b * f = f * b) :
    ∀ b ∈ B, b * (a⁻¹ * e * a) = (a⁻¹ * e * a) * b → b * (a⁻¹ * f * a) = (a⁻¹ * f * a) * b := by
  intro b hb hbe
  have hb' : a * b * a⁻¹ ∈ B := Subgroup.Normal.conj_mem inferInstance b hb a
  have h1 : (a * b * a⁻¹) * e = e * (a * b * a⁻¹) := by
    calc (a * b * a⁻¹) * e = a * (b * (a⁻¹ * e * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * e * a) * b) * a⁻¹ := by rw [hbe]
      _ = e * (a * b * a⁻¹) := by group
  have h2 := h _ hb' h1
  calc b * (a⁻¹ * f * a) = a⁻¹ * ((a * b * a⁻¹) * f) * a := by group
    _ = a⁻¹ * (f * (a * b * a⁻¹)) * a := by rw [h2]
    _ = (a⁻¹ * f * a) * b := by group

end Star

section Centralizes

variable {Y : Type} [Group Y] (N : Subgroup Y) [N.Normal] (E : Subgroup (Y ⧸ N))

theorem core_centralizes [Finite Y] [E.Normal] (hNodd : Odd (Nat.card N)) (hEs : IsSimpleGroup E)
    {P : Subgroup Y} [hPn : P.Normal] (hPsup : P ⊔ N = E.comap (QuotientGroup.mk' N))
    (hPperf : ⁅P, P⁆ = P) {z u a : Y} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu2 : u * u = 1)
    (hzne : z ≠ u) (hzu : z * u = u * z) (hzP : z ∈ P) (ha1 : a⁻¹ * z * a = u) (ha2 : a⁻¹ * u * a = z * u)
    (hstar : ∀ b ∈ P ⊓ N, b * z = z * b → b * u = u * b) :
    ∀ b ∈ P ⊓ N, ∀ p ∈ P, b * p = p * b := by
  classical
  have hPmap := map_eq_of_sup N E hPsup
  set B : Subgroup Y := P ⊓ N with hB
  have hBn : B.Normal := inferInstance
  have hBodd : Odd (Nat.card B) := Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_right)
  have hBsolv : Group.IsSolvable B := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hBodd
  have hBP : B ≤ P := inf_le_left
  set C : Subgroup Y := Subgroup.centralizer (B : Set Y) ⊓ P with hC
  have hCP : C ≤ P := inf_le_right
  have hCn : ∀ g ∈ P, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, P.mul_mem (P.mul_mem hg hc.2) (P.inv_mem hg)⟩
    intro b hb
    have hb' : g⁻¹ * b * g ∈ B := by
      have := Subgroup.Normal.conj_mem hBn b hb g⁻¹
      simpa using this
    have hcb := (Subgroup.mem_centralizer_iff.1 hc.1) _ hb'
    calc b * (g * c * g⁻¹) = g * ((g⁻¹ * b * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * b * g)) * g⁻¹ := by rw [hcb]
      _ = (g * c * g⁻¹) * b := by group
  have hCBn : ∀ g ∈ P, ∀ m ∈ C ⊔ B, g * m * g⁻¹ ∈ C ⊔ B := by
    intro g hg m hm
    have hmul := Subgroup.mem_sup_of_normal_right (s := C) (t := B) (x := m)
    obtain ⟨c, hc, b, hb, rfl⟩ := hmul.1 hm
    have e : g * (c * b) * g⁻¹ = (g * c * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hCn g hg c hc))
      (Subgroup.mem_sup_right (Subgroup.Normal.conj_mem hBn b hb g))
  have hCBP : C ⊔ B ≤ P := sup_le hCP hBP
  rcases maximal_normal_of_simple N E hEs hPmap (C ⊔ B) hCBP hCBn (le_sup_right) with h | h
  ·
    rw [← hB] at h
    exfalso
    have hCB : C ≤ B := by rw [← h]; exact le_sup_left
    have hzC : z ∈ C := by
      refine ⟨Subgroup.mem_centralizer_iff.2 ?_, hzP⟩
      intro b hb
      have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
      have hu1 : u ≠ 1 := by
        intro h1
        rw [h1] at ha1
        apply hz1
        have : z = a * (a⁻¹ * z * a) * a⁻¹ := by group
        rw [ha1] at this
        simpa using this
      have hT12 := star_transfer (B := B) (a := a) (e := z) (f := u) hstar
      rw [ha1, ha2] at hT12
      have hT20 := star_transfer (B := B) (a := a) (e := u) (f := z * u) hT12
      have hzu_a : a⁻¹ * (z * u) * a = z := by
        calc a⁻¹ * (z * u) * a = (a⁻¹ * z * a) * (a⁻¹ * u * a) := by group
          _ = u * (z * u) := by rw [ha1, ha2]
          _ = z := by
              calc u * (z * u) = (u * z) * u := by group
                _ = (z * u) * u := by rw [hzu]
                _ = z * (u * u) := by group
                _ = z := by rw [hu2, mul_one]
      rw [ha2, hzu_a] at hT20
      have hcz : ∀ w ∈ t2U z u, w ≠ 1 → ∀ b ∈ B, b * w = w * b → b * z = z * b := by
        intro w hw hw1 b hb hbw
        rcases (t2U_mem hz2 hu2 hzu).1 hw with h1 | h1 | h1 | h1
        · exact absurd h1 hw1
        · rw [h1] at hbw; exact hbw
        · rw [h1] at hbw
          have h2 := hT12 b hb hbw
          have h3 := hT20 b hb h2
          exact h3
        · rw [h1] at hbw
          exact hT20 b hb hbw
      have hW2 : ∀ w ∈ t2U z u, w * w = 1 := by
        intro w hw
        rcases (t2U_mem hz2 hu2 hzu).1 hw with h1 | h1 | h1 | h1
        · rw [h1]; group
        · rw [h1]; exact hz2
        · rw [h1]; exact hu2
        · rw [h1]
          calc z * u * (z * u) = z * (u * z) * u := by group
            _ = z * (z * u) * u := by rw [hzu]
            _ = (z * z) * (u * u) := by group
            _ = 1 := by rw [hz2, hu2, one_mul]
      have hWz : ∀ w ∈ t2U z u, w * z = z * w := by
        intro w hw
        rcases (t2U_mem hz2 hu2 hzu).1 hw with h1 | h1 | h1 | h1
        · rw [h1]; group
        · rw [h1]
        · rw [h1]; exact hzu.symm
        · rw [h1]
          calc z * u * z = z * (u * z) := by group
            _ = z * (z * u) := by rw [hzu]
      have hgen := CFSG.GH74.Uniqueness.commutator_zpowers_eq_iSup (X := Y) (Y := B) (W := t2U z u)
        (t := z) hBodd hz2' (mem_normalizer_of_normal B z)
        (t2U_card hz2 hu2 hzu hz1 hu1 hzne) hW2 (fun w _ => mem_normalizer_of_normal B w)
        (fun w hw => by rw [Subgroup.mem_centralizer_singleton_iff]; exact hWz w hw)
      have hbot : ⁅Subgroup.zpowers z, B⁆ = ⊥ := by
        rw [hgen]
        refine iSup₂_eq_bot.2 fun w hw => ?_
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le]
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxw : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.1 hx.1
        exact hcz w hw.1 hw.2 x hx.2 hxw
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le] at hbot
      exact Subgroup.mem_centralizer_iff.1 hbot b hb
    have hzB : z ∈ B := hCB hzC
    have hzN : z ∈ N := hzB.2
    have := eq_one_of_sq_eq_one_of_odd hNodd hzN hz2
    exact hz1 this
  ·
    have hPC : P ≤ C := by
      have hCnorm : (C.subgroupOf P).Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hCn g g.2 n hn⟩
      have := hCnorm
      have hPperf' : Group.IsPerfect P := Subgroup.isPerfect_iff.2 hPperf
      have hPbperf : Group.IsPerfect (↥P ⧸ C.subgroupOf P) :=
        Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (C.subgroupOf P))
      let f : ↥B →* (↥P ⧸ C.subgroupOf P) :=
        (QuotientGroup.mk' (C.subgroupOf P)).comp (Subgroup.inclusion hBP)
      have hf : Function.Surjective f := by
        intro q
        obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
        have hp : (p : Y) ∈ C ⊔ B := by rw [h]; exact p.2
        obtain ⟨c, hc, b, hb, hcb⟩ := (Subgroup.mem_sup_of_normal_right (s := C) (t := B)).1 hp
        refine ⟨⟨b, hb⟩, ?_⟩
        show (QuotientGroup.mk (⟨b, hBP hb⟩ : ↥P) : ↥P ⧸ C.subgroupOf P) = QuotientGroup.mk p
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hb1 : b⁻¹ * c⁻¹ * b ∈ C := by
          have := hCn b⁻¹ (P.inv_mem (hBP hb)) c⁻¹ (C.inv_mem hc)
          simpa using this
        have hpe : (p : Y) = c * b := hcb.symm
        show (b : Y)⁻¹ * (p : Y) ∈ C
        rw [hpe]
        have e : b⁻¹ * (c * b) = b⁻¹ * c * b := by group
        rw [e]
        have := hCn b⁻¹ (P.inv_mem (hBP hb)) c hc
        simpa using this
      have hsolv : Group.IsSolvable (↥P ⧸ C.subgroupOf P) := Group.isSolvable_of_surjective hf
      have hsub : Subsingleton (↥P ⧸ C.subgroupOf P) := by
        by_contra hns
        have : Nontrivial (↥P ⧸ C.subgroupOf P) := not_subsingleton_iff_nontrivial.1 hns
        exact Group.IsPerfect.not_isSolvable _ hsolv
      intro p hp
      have h1 : (QuotientGroup.mk (⟨p, hp⟩ : ↥P) : ↥P ⧸ C.subgroupOf P) = 1 := Subsingleton.elim _ _
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    intro b hb p hp
    exact (Subgroup.mem_centralizer_iff.1 (hPC hp).1) b hb

end Centralizes

section Schur

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem psl3_not_comm :
    ¬ ∀ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F, a * b = b * a := by
  intro h
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := F) (n := 3) (by norm_num) (Or.inl le_rfl)
  have hnt := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by norm_num) (Or.inl le_rfl)).1
  have : IsMulCommutative (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := ⟨⟨fun a b => h a b⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ this

omit [Finite F] in
theorem ker_le_center_of_surj {G' : Type} [Group G'] (β : SL(3, F) →* G')
    (hβ : Function.Surjective β) (hnc : ¬ ∀ a b : G', a * b = b * a) :
    β.ker ≤ Subgroup.center SL(3, F) := by
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  set Z := Subgroup.center SL(3, F) with hZ
  let q : SL(3, F) →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F := QuotientGroup.mk' Z
  have hn : (β.ker.map q).Normal :=
    Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective Z)
  have := hn
  rcases hsimple.eq_bot_or_eq_top_of_normal (β.ker.map q) with h | h
  · intro k hk
    have : q k ∈ β.ker.map q := ⟨k, hk, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff k).1 this
  · exfalso
    apply hnc
    have key : ∀ x : SL(3, F), ∃ w ∈ Z, β x = β w := by
      intro x
      have hx : q x ∈ β.ker.map q := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := hx
      have hxZ : k⁻¹ * x ∈ Z := QuotientGroup.eq.1 hkx
      refine ⟨k⁻¹ * x, hxZ, ?_⟩
      have hk1 : β k = 1 := hk
      rw [map_mul, map_inv, hk1]
      simp
    intro a b
    obtain ⟨x, rfl⟩ := hβ a
    obtain ⟨y, rfl⟩ := hβ b
    obtain ⟨w₁, hw₁, e₁⟩ := key x
    obtain ⟨w₂, hw₂, e₂⟩ := key y
    rw [e₁, e₂, ← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.1 hw₂ w₁)

theorem sl3_image_eq {P : Type} [Group P] (α : SL(3, F) →* P) (hα : Function.Surjective α)
    (hker : α.ker ≤ Subgroup.center SL(3, F)) :
    IsSLnEps 3 P 1 (Nat.card F) ∨ IsLnEps 3 P 1 (Nat.card F) := by
  have hZ : Nat.card (Subgroup.center SL(3, F)) ∣ 3 := by
    rw [OrderReductions.LinearOrders.card_specialLinear_center F 3 (by norm_num)]
    exact Nat.gcd_dvd_left _ _
  have hK : Nat.card α.ker ∣ 3 := (Subgroup.card_dvd_of_le hker).trans hZ
  rcases (Nat.dvd_prime Nat.prime_three).1 hK with h1 | h3
  · left
    have hbot : α.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hinj : Function.Injective α := (injective_iff_map_eq_one α).2 fun x hx => by
      have : x ∈ α.ker := hx
      rw [hbot] at this
      exact this
    exact Or.inl ⟨rfl, F, inferInstance, inferInstance, rfl,
      ⟨(MulEquiv.ofBijective α ⟨hinj, hα⟩).symm.trans (specialLinearGroupEquivStatedSL 3 F)⟩⟩
  · right
    have hZle : Nat.card (Subgroup.center SL(3, F)) ≤ Nat.card α.ker := by
      rw [h3]; exact Nat.le_of_dvd (by norm_num) hZ
    have hKZ : α.ker = Subgroup.center SL(3, F) := Subgroup.eq_of_le_of_card_ge hker hZle
    exact Or.inl ⟨rfl, F, inferInstance, inferInstance, rfl,
      ⟨((QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hKZ)).trans
          (projectiveSpecialLinearGroupEquivStatedProj 3 F)⟩⟩

end Schur

section CoverAt

@[expose] def L3CoverAt (q : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsLnEps 3 J 1 q → ∀ (E : Type) [Group E] [Finite E],
    Group.IsPerfect E → ∀ π : E →* J, Function.Surjective π → π.ker ≤ Subgroup.center E →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
        ∃ α : SL(3, F) →* E, Function.Surjective α

theorem l3CoverAt_of_l3Cover (hL3 : LU.Local.L3Cover) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ n) : L3CoverAt (p ^ n) := by
  intro J _ _ hJ E _ _ hE π hπ hker
  exact (hL3 J 1 p n hp hp2 (Or.inl rfl) h5 hJ E hE π hπ hker).1 rfl

end CoverAt

section SchurStep

variable {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal] (E : Subgroup (Y ⧸ N))

theorem schur_step_gen {q : ℕ} (hcov : L3CoverAt q) [E.Normal] (hE : IsLnEps 3 ↥E 1 q)
    {P : Subgroup Y} [P.Normal]
    (hPmap : P.map (QuotientGroup.mk' N) = E) (hPperf : ⁅P, P⁆ = P)
    (hBc : ∀ b ∈ P ⊓ N, ∀ x ∈ P, b * x = x * b) :
    IsSLnEps 3 ↥P 1 q ∨ IsLnEps 3 ↥P 1 q := by
  set π := QuotientGroup.mk' N with hπ
  let π' : ↥P →* ↥E := ((π.comp P.subtype).codRestrict E fun x => by
    rw [← hPmap]; exact ⟨x, x.2, rfl⟩)
  have hπ'surj : Function.Surjective π' := by
    intro e
    have : (e : Y ⧸ N) ∈ P.map π := by rw [hPmap]; exact e.2
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hker : π'.ker ≤ Subgroup.center ↥P := by
    intro x hx
    have h1 : π (x : Y) = 1 := congrArg Subtype.val hx
    have hxN : (x : Y) ∈ N := (QuotientGroup.eq_one_iff (x : Y)).1 h1
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hBc x ⟨x.2, hxN⟩ g g.2).symm
  have hPperf' : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hPperf
  obtain ⟨F, iF, iFin, hF, α, hα⟩ := hcov ↥E hE ↥P hPperf' π' hπ'surj hker
  have hEnc : ¬ ∀ a b : ↥E, a * b = b * a := by
    obtain ⟨-, F₀, iF₀, iFin₀, hF₀, ⟨e⟩⟩ := (hE.resolve_right (by rintro ⟨h, -⟩; norm_num at h))
    intro hc
    apply psl3_not_comm (F := F₀)
    intro a b
    have := hc (e.symm ((projectiveSpecialLinearGroupEquivStatedProj 3 F₀) a))
      (e.symm ((projectiveSpecialLinearGroupEquivStatedProj 3 F₀) b))
    have h2 := congrArg ((projectiveSpecialLinearGroupEquivStatedProj 3 F₀).symm ∘ e) this
    simpa using h2
  have hker' : (π'.comp α).ker ≤ Subgroup.center SL(3, F) :=
    ker_le_center_of_surj (π'.comp α) (hπ'surj.comp hα) hEnc
  have hkα : α.ker ≤ Subgroup.center SL(3, F) := by
    intro x hx
    apply hker'
    have : α x = 1 := hx
    simp [MonoidHom.mem_ker, this]
  have := sl3_image_eq α hα hkα
  rw [hF] at this
  exact this

theorem isLnEps_one_facts {E : Type} [Group E] {q : ℕ} (hE : IsLnEps 3 E 1 q) :
    IsSimpleGroup E ∧ Group.IsPerfect E := by
  obtain ⟨-, F₀, iF₀, iFin₀, hF₀, ⟨e⟩⟩ := hE.resolve_right (by rintro ⟨h, -⟩; norm_num at h)
  have hs := (CFSG.LinearGroups.linear_projective_simple (K := F₀) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  have hp := CFSG.LinearGroups.linear_projective_perfect (K := F₀) (n := 3) (by norm_num)
    (Or.inl le_rfl)
  let e' : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F₀ ≃* E :=
    ((projectiveSpecialLinearGroupEquivStatedProj 3 F₀).trans e.symm)
  have := hs
  have := hp
  exact ⟨e'.symm.isSimpleGroup, Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective⟩

theorem schur_step (hL3 : LU.Local.L3Cover) [E.Normal] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ n) (hE : IsLnEps 3 ↥E 1 (p ^ n)) {P : Subgroup Y} [P.Normal]
    (hPmap : P.map (QuotientGroup.mk' N) = E) (hPperf : ⁅P, P⁆ = P)
    (hBc : ∀ b ∈ P ⊓ N, ∀ x ∈ P, b * x = x * b) :
    IsSLnEps 3 ↥P 1 (p ^ n) ∨ IsLnEps 3 ↥P 1 (p ^ n) :=
  schur_step_gen N E (l3CoverAt_of_l3Cover hL3 hp hp2 h5) hE hPmap hPperf hBc

end SchurStep

section Lift

variable {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal] (E : Subgroup (Y ⧸ N))

theorem lift_core (hL3 : LU.Local.L3Cover) [E.Normal] (hNodd : Odd (Nat.card N)) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ n) (hE : IsLnEps 3 ↥E 1 (p ^ n)) {K : Subgroup Y} (hK : ⁅K, K⁆ = K)
    (hKE : K.map (QuotientGroup.mk' N) ≤ E) {z u a : Y} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hu2 : u * u = 1) (hzne : z ≠ u) (hzu : z * u = u * z) (hzK : z ∈ K) (ha1 : a⁻¹ * z * a = u)
    (ha2 : a⁻¹ * u * a = z * u)
    (hstar : ∀ B : Subgroup Y, B.Normal → B ≤ N → ∀ b ∈ B, b * z = z * b → b * u = u * b) :
    ∃ P : Subgroup Y, K ≤ P ∧ (IsSLnEps 3 ↥P 1 (p ^ n) ∨ IsLnEps 3 ↥P 1 (p ^ n)) := by
  obtain ⟨hEs, hEperf⟩ := isLnEps_one_facts hE
  have hEc : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 hEperf
  obtain ⟨P, hPn, hPle, hPsup, hPperf⟩ := exists_perfect_core N E hEc
  have hKP : K ≤ P := perfect_le_core N E hNodd hPsup hK hKE
  have hPmap := map_eq_of_sup N E hPsup
  have hBc := core_centralizes N E hNodd hEs hPsup hPperf hz2 hz1 hu2 hzne hzu (hKP hzK) ha1 ha2
    (fun b hb => hstar (P ⊓ N) inferInstance inf_le_right b hb)
  exact ⟨P, hKP, schur_step N E hL3 hp hp2 h5 hE hPmap hPperf hBc⟩

theorem lift_core_gen {q : ℕ} (hcov : L3CoverAt q) [E.Normal] (hNodd : Odd (Nat.card N))
    (hE : IsLnEps 3 ↥E 1 q) {K : Subgroup Y}
    (hKP : ∀ P : Subgroup Y, P.Normal → P ⊔ N = E.comap (QuotientGroup.mk' N) → K ≤ P)
    {z u a : Y} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu2 : u * u = 1) (hzne : z ≠ u)
    (hzu : z * u = u * z) (hzK : z ∈ K) (ha1 : a⁻¹ * z * a = u) (ha2 : a⁻¹ * u * a = z * u)
    (hstar : ∀ B : Subgroup Y, B.Normal → B ≤ N → ∀ b ∈ B, b * z = z * b → b * u = u * b) :
    ∃ P : Subgroup Y, K ≤ P ∧ (IsSLnEps 3 ↥P 1 q ∨ IsLnEps 3 ↥P 1 q) := by
  obtain ⟨hEs, hEperf⟩ := isLnEps_one_facts hE
  have hEc : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 hEperf
  obtain ⟨P, hPn, hPle, hPsup, hPperf⟩ := exists_perfect_core N E hEc
  have hKP' : K ≤ P := hKP P hPn hPsup
  have hPmap := map_eq_of_sup N E hPsup
  have hBc := core_centralizes N E hNodd hEs hPsup hPperf hz2 hz1 hu2 hzne hzu (hKP' hzK) ha1 ha2
    (fun b hb => hstar (P ⊓ N) inferInstance inf_le_right b hb)
  exact ⟨P, hKP', schur_step_gen N E hcov hE hPmap hPperf hBc⟩

end Lift

end CFSG.GH74.GLS.Stage4.Rest
