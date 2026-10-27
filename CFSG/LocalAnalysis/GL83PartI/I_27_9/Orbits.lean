module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Count
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Rank
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.OrbitBound
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.GenAlt
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace GL83.PiGen

open Equiv Equiv.Perm MulAction GL83.CompFam CFSG.Open

section Transport

variable {X : Type*} [Group X] [Finite X] {K : Subgroup X}

omit [Finite X] in
theorem isElemAbelian_subgroupOf {p : ℕ} {V A : Subgroup X} (hV : IsElemAbelian p V) :
    IsElemAbelian p (V.subgroupOf A) := CFSG.Open.IsElemAbelian.subgroupOf hV A

omit [Finite X] in
theorem exists_klein_elem_in_component {p n : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (hn : 4 ≤ n)
    (φ : K ≃* alternatingGroup (Fin n)) :
    ∃ V E₀ : Subgroup X, V ≤ K ∧ E₀ ≤ K ∧ V ≠ ⊥ ∧ IsElemAbelian 2 V ∧ IsElemAbelian p E₀ ∧
      E₀ ≤ Subgroup.normalizer (V : Set X) ∧
      p ^ ((n - 4) / p + if p = 3 then 1 else 0) ≤ Nat.card E₀ := by
  obtain ⟨V, E₀, hVA, hV0, hV2, hEA, hEel, hEN, hcard⟩ :=
    exists_klein_elem (Ω := Fin n) hp3 (by simpa using hn)
  let ψ : alternatingGroup (Fin n) →* X := K.subtype.comp φ.symm.toMonoidHom
  have hψ : Function.Injective ψ :=
    K.subtype_injective.comp φ.symm.injective
  have hψK : ∀ v, ψ v ∈ K := fun v => (φ.symm v).2
  refine ⟨(V.subgroupOf (alternatingGroup (Fin n))).map ψ,
    (E₀.subgroupOf (alternatingGroup (Fin n))).map ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, -, rfl⟩
    exact hψK v
  · rintro _ ⟨v, -, rfl⟩
    exact hψK v
  · intro h
    rw [Subgroup.map_eq_bot_iff_of_injective _ hψ] at h
    apply hV0
    have := congrArg (Subgroup.map (alternatingGroup (Fin n)).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hVA, Subgroup.map_bot] at this
  · exact CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hV2) ψ
  · exact CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hEel) ψ
  · refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map ψ)
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    have h1 := Subgroup.mem_normalizer_iff.1 (hEN (Subgroup.mem_subgroupOf.1 hg)) (m : Perm (Fin n))
    exact Subgroup.mem_subgroupOf.2 (h1.1 (Subgroup.mem_subgroupOf.1 hm))
  · rw [Subgroup.card_map_of_injective hψ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv]
    simpa only [Fintype.card_fin] using hcard

end Transport

section Main

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem card_eq_pow_pRank {B : Subgroup X} (hB : IsElemAbelian p B) :
    Nat.card B = p ^ pRank p B := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨k, hk⟩ := exists_card_eq_pow hB
  have h1 : k ≤ pRank p B := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB hk
  have h2 : pRank p B ≤ k := CFSG.SectionRank.pRank_le hp.one_lt fun E hEB _ =>
    hk ▸ Subgroup.card_le_of_le hEB
  rw [hk, le_antisymm h1 h2]

omit [Finite X] in
theorem stab_le_normalizer (B K : Subgroup X) : stab B K ≤ Subgroup.normalizer (K : Set X) :=
  inf_le_right

omit [Finite X] in
theorem card_stab_eq_mul {B K : Subgroup X} [Group.IsPerfect K] {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    Nat.card (stab B K) = Nat.card (cen B K) *
      Nat.card (permHom (stab_le_normalizer B K) hn hn6 e).range := by
  set π := permHom (stab_le_normalizer B K) hn hn6 e with hπ
  have h1 := Subgroup.card_ker_mul_card_range π
  have hker : π.ker.map (stab B K).subtype = cen B K := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hc := (permHom_eq_one_iff (stab_le_normalizer B K) hn hn6 e a).1 (MonoidHom.mem_ker.1 ha)
      exact mem_cen.2 ⟨(mem_stab.1 a.2).1, fun y hy => hc ⟨y, hy⟩⟩
    · intro hx
      obtain ⟨hxB, hxc⟩ := mem_cen.1 hx
      refine ⟨⟨x, cen_le_stab B K hx⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
      exact (permHom_eq_one_iff (stab_le_normalizer B K) hn hn6 e _).2 fun y => hxc y y.2
  have h2 : Nat.card π.ker = Nat.card (cen B K) := by
    rw [← hker]
    exact (Subgroup.card_map_of_injective (stab B K).subtype_injective).symm
  rw [← h1, h2]

omit [Fact p.Prime] [Finite X] in
theorem inf_centralizer_eq_bot_of_center_eq_bot {K : Subgroup X} (hZ : Subgroup.center K = ⊥) :
    K ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxK, hxc⟩ := hx
  have : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)
  rw [hZ, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)

omit [Fact p.Prime] [Finite X] in
theorem exists_mulEquiv_of_center_eq_bot {K : Subgroup X} {n : ℕ} (hZ : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    Nonempty (K ≃* alternatingGroup (Fin n)) := by
  refine ⟨MulEquiv.ofBijective
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) ⟨?_, ?_⟩⟩
  · intro x y hxy
    have h1 : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = QuotientGroup.mk y := e.injective hxy
    have h2 := QuotientGroup.eq.1 h1
    rw [hZ, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.1 h2
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem orbit_le_card {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (R : Subgroup (Perm Ω)) (ω : Ω) :
    Nat.card (orbit R ω) ≤ Nat.card R := by
  rw [card_mul_card_stabIn R ω]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem orbit_card_le (hp3 : 3 ≤ p) {B K : Subgroup X} {k n : ℕ} (hk : 1 ≤ k)
    (hnk : n = k * p + 2) (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hB : IsElemAbelian p B)
    (hK : IsComponentOf K ⊤) (hZ : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hrank : GLATwoLocalRank p X ≤ pRank p B) (ω : Fin n) :
    Nat.card (orbit (permHom (stab_le_normalizer B K) hn5 hn6 e).range ω) ≤ p := by
  have hp := (Fact.out : p.Prime)
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  set π := permHom (stab_le_normalizer B K) hn5 hn6 e with hπ
  set R := π.range with hR
  have hAB : stab B K ≤ B := inf_le_left
  have hAel : IsElemAbelian p (stab B K) := elem_mono hB hAB
  have hRel : IsElemAbelian p R := isElemAbelian_range hAel π
  have hRpg : IsPGroup p R := isPGroup_of_elem hRel
  obtain ⟨r, hr⟩ := exists_card_eq_pow hRel
  have hdiv : Fintype.card (Fin n) / p = k := by
    rw [Fintype.card_fin, hnk]
    exact Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  have hRk : Nat.card R ≤ p ^ k := by
    have h := CFSG.AGLEmbedding.card_le_pow_div_of_commute (p := p) R
      (fun x hx y hy => elem_comm hRel hx hy) hRpg
    rwa [hdiv] at h
  by_cases hk1 : k = 1
  · subst hk1
    calc Nat.card (orbit R ω) ≤ Nat.card R := orbit_le_card R ω
      _ ≤ p ^ 1 := hRk
      _ = p := pow_one p
  · have hk2 : 2 ≤ k := by omega
    by_contra hlt
    obtain ⟨s, hs⟩ := hRpg.card_orbit ω
    have hs2 : 2 ≤ s := by
      by_contra hs1
      have : p ^ s ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      rw [pow_one] at this
      exact hlt (hs ▸ this)
    have hP := rank_add_pow_le hRel ω (k := k) (by rw [Fintype.card_fin]; exact hnk) hp3
      (by omega) hs hr
    have hrk : r ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hr ▸ hRk)
    obtain ⟨φ⟩ := exists_mulEquiv_of_center_eq_bot hZ e
    obtain ⟨V, E₀, hVK, hEK, hV0, hV2, hEel, hEV, hE₀⟩ :=
      exists_klein_elem_in_component (K := K) hp3 (by omega : 4 ≤ n) φ
    have hcount := card_conj_family_le hB hK (inf_centralizer_eq_bot_of_center_eq_bot hZ) hVK hEK
      hV0 hV2 hEel hEV
    have h1 : p ^ GLATwoLocalRank p X ≤ Nat.card B := by
      rw [card_eq_pow_pRank hB]
      exact Nat.pow_le_pow_right hp.pos hrank
    set t := (stab B K).relIndex B with ht
    have hBt : Nat.card B = t * Nat.card (stab B K) := by
      have h := Subgroup.relIndex_mul_card (H := stab B K) (K := B)
      rw [inf_eq_left.2 hAB] at h
      exact h.symm
    have hAC : Nat.card (stab B K) = Nat.card (cen B K) * Nat.card R :=
      card_stab_eq_mul hn5 hn6 e
    have hCpos : 0 < Nat.card (cen B K) := Nat.card_pos
    have h2 : Nat.card E₀ ^ t ≤ t * Nat.card R := by
      have : Nat.card (cen B K) * Nat.card E₀ ^ t ≤ Nat.card (cen B K) * (t * Nat.card R) := by
        calc Nat.card (cen B K) * Nat.card E₀ ^ t ≤ p ^ GLATwoLocalRank p X := hcount
          _ ≤ Nat.card B := h1
          _ = Nat.card (cen B K) * (t * Nat.card R) := by rw [hBt, hAC]; ring
      exact Nat.le_of_mul_le_mul_left this hCpos
    obtain ⟨a, -, hta⟩ : ∃ a ≤ pRank p B, t = p ^ a := by
      refine (Nat.dvd_prime_pow hp).1 ?_
      rw [← card_eq_pow_pRank hB, hBt]
      exact Dvd.intro _ rfl
    have h3 : (p ^ ((n - 4) / p + if p = 3 then 1 else 0)) ^ t ≤ p ^ (a + r) := by
      calc (p ^ ((n - 4) / p + if p = 3 then 1 else 0)) ^ t ≤ Nat.card E₀ ^ t :=
            Nat.pow_le_pow_left hE₀ t
        _ ≤ t * Nat.card R := h2
        _ = p ^ (a + r) := by rw [hta, hr, pow_add]
    have h4 : ((n - 4) / p + if p = 3 then 1 else 0) * t ≤ a + r := by
      rw [← pow_mul] at h3
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h3
    have hdiv4 : (n - 4) / p = k - 1 := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [hnk, show (k' + 1) * p + 2 - 4 = k' * p + (p - 2) by
        rw [add_mul]; omega]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt (by omega)]
      simp
    rw [hdiv4, hta] at h4
    have hp' : p = 3 ∨ 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with h | h
      · have : p = 3 ∨ p = 4 := by omega
        rcases this with h3 | h4
        · exact Or.inl h3
        · exact absurd (h4 ▸ hp) (by norm_num)
      · exact Or.inr h
    exact no_big_orbit_arith hp' hk2 hrk hs2 h4 hP

end Main

end GL83.PiGen
