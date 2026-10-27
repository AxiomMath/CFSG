module

public import CFSG.GF2Type.SmithTypeE.L6.TrRep

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup Module CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod
  CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial Matrix
open CFSG.LargeExtraspecial.SMod20 (V decode decode_xor decode_zero bit)
open scoped MatrixGroups

attribute [local irreducible] tvIdxTab tvTab tvImg tvList planePtsArr flagArr wtArr maskArr annArr

theorem decode_two_pow (t : Fin 20) : decode (2 ^ t.val) = fun j => if t = j then 1 else 0 := by
  funext j
  rw [CFSG.LargeExtraspecial.SMod20.decode_apply, Nat.testBit_two_pow]
  by_cases h : t = j
  · simp [h]
  · simp [h, Fin.val_ne_of_ne h]

theorem span_eq_top_of_units {ws : List ℕ} (h : ∀ t < 20, ∃ m, trXorSel ws m = 2 ^ t) :
    Submodule.span (ZMod 2) {u | ∃ w ∈ ws, u = decode w} = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [pi_eq_sum_univ v]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
  obtain ⟨m, hm⟩ := h t.val t.2
  rw [← decode_two_pow, ← hm]
  refine decode_trXorSel_mem ws (fun w hw => ?_) m
  have hw' : decode w ∈ {u : V | ∃ w' ∈ ws, u = decode w'} := ⟨w, hw, rfl⟩
  exact Submodule.subset_span hw'

variable
  {A : V ≃ₗ[ZMod 2] V} {π : Equiv.Perm (Fin 1953)}

theorem eq_one_of_fix6 {ρ : Equiv.Perm (Fin 1953)} (hρ : ρ ∈ T6) {b6 : List ℕ} (hl : b6.length = 6)
    (hfix : ∀ x ∈ b6, ∃ hx : x < 1953, ρ ⟨x, hx⟩ = ⟨x, hx⟩)
    (hind : ∀ m, 0 < m → m < 64 → trXorSel (b6.map fun x => (tvPair x).1) m ≠ 0) : ρ = 1 := by
  obtain ⟨B, rfl⟩ := exists_actPerm_eq hρ
  have hB : (B : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    refine eq_one_of_selIndep (vs := b6.map fun x => (tvPair x).1) (by rw [List.length_map, hl])
      (fun b hb => ?_) (fun m hm0 hm => hind m hm0 (by rwa [List.length_map, hl] at hm))
      (fun b hb => ?_)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
      obtain ⟨hx', _⟩ := hfix x hx
      exact (CFSG.SmithL6.K.tvP_tvPair hx').1
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
      obtain ⟨hx', he⟩ := hfix x hx
      have e := tvVec_actPerm B ⟨x, hx'⟩
      rw [he] at e
      exact e.symm
  have hB1 : B = 1 := Subtype.ext hB
  rw [hB1, map_one]

theorem fp_of_outer (h : InvHyp A π) {ct : Array ℕ} (hc : IsTab ct π) {bs : List ℕ}
    (hbs : bs.length ≤ 8) {pl : List (ℕ × ℕ)}
    (hpl : ∀ q ∈ pl, q.1 < 1395 ∧ q.2 < 1395 ∧
      (∀ x < 1953, inPlane q.1 x = true → inPlane q.2 ct[x]! = true) ∧
      ∃ m, trXorSel bs m = wt q.2 ^^^ wt q.1)
    (hum : ∀ t < 20, ∃ m, trXorSel (pl.map fun q => wt q.1) m = 2 ^ t)
    (hodd : (trFixL ct).length % 2 = 1)
    (horb : ∃ q₀ ∈ trFixL ct, ∀ Q : ℕ → Prop, Q q₀ →
      (∀ q ∈ trFixL ct, ∀ u ∈ trFixL ct, Q u → Q (tvImg q u)) → ∀ v ∈ trFixL ct, Q v)
    {b6 : List ℕ} (hb6l : b6.length = 6) (hb6 : ∀ x ∈ b6, x ∈ trFixL ct)
    (hind : ∀ m, 0 < m → m < 64 → trXorSel (b6.map fun x => (tvPair x).1) m ≠ 0) :
    finrank (ZMod 2) (commSpace A) ≤ 8 ∧ NoTwoSub π := by
  have hπ : IsTvAut π := isTvAut_of_mem_normalizer h.norm
  have hfx : ∀ q, q ∈ trFixL ct ↔ ∃ hq : q < 1953, π ⟨q, hq⟩ = ⟨q, hq⟩ := fun q => mem_trFixL hc
  set S := Submodule.span (ZMod 2) {u | ∃ v ∈ bs, u = decode v}
  have hsub : ∀ v, A v - v ∈ S := by
    intro v
    have hv : v ∈ Submodule.span (ZMod 2) {u | ∃ w ∈ pl.map (fun q => wt q.1), u = decode w} := by
      rw [span_eq_top_of_units hum]
      trivial
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hw
      obtain ⟨hi, hi', hp, m, hm⟩ := hpl q hq
      have e : A (decode (wt q.1)) - decode (wt q.1) = decode (wt q.2 ^^^ wt q.1) := by
        rw [decode_xor, sub_eq_add_V]
        change A (wtV q.1) + wtV q.1 = wtV q.2 + wtV q.1
        rw [h.wtV_eq hi hi' (image_of_tab hc hi hi' hp)]
      rw [e, ← hm]
      refine decode_trXorSel_mem bs (fun v hv => ?_) m
      have hv' : decode v ∈ {u : V | ∃ w' ∈ bs, u = decode w'} := ⟨v, hv, rfl⟩
      exact Submodule.subset_span hv'
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, show A x + A y - (x + y) = (A x - x) + (A y - y) by abel]
      exact S.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul, ← smul_sub]
      exact S.smul_mem a hx
  have hYle : commSpace A ≤ S := by
    rintro _ ⟨v, rfl⟩
    exact hsub v
  refine ⟨(Submodule.finrank_mono hYle).trans ((finrank_span_decode_le bs).trans hbs), ?_⟩
  intro R hRT hRp hRc hRn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction R {x : Fin 1953 // π x = x} :=
    { smul := fun r x => ⟨(r : Equiv.Perm (Fin 1953)) x.1, by
        have e := hRc r.1 r.2
        calc π ((r : Equiv.Perm (Fin 1953)) x.1) = (π * (r : Equiv.Perm (Fin 1953))) x.1 := rfl
          _ = ((r : Equiv.Perm (Fin 1953)) * π) x.1 := by rw [e]
          _ = (r : Equiv.Perm (Fin 1953)) x.1 := by
            change (r : Equiv.Perm (Fin 1953)) (π x.1) = _
            rw [x.2]⟩
      one_smul := fun x => Subtype.ext rfl
      mul_smul := fun r s x => Subtype.ext rfl }
  have hX : ¬ 2 ∣ Nat.card {x : Fin 1953 // π x = x} := by
    rw [card_fixedPoints_eq hc]
    omega
  obtain ⟨x₀, hx₀⟩ := hRp.nonempty_fixed_point_of_prime_not_dvd_card
    {x : Fin 1953 // π x = x} hX
  let P : Fin 1953 → Prop := fun v => ∀ r ∈ R, r v = v
  have hP : ∀ p ∈ trFixL ct, ∀ (hp : p < 1953) (u : Fin 1953), P u → P (tvP ⟨p, hp⟩ u) := by
    intro p hpf hp u hu r hr
    have hpfix : π ⟨p, hp⟩ = ⟨p, hp⟩ := by
      obtain ⟨_, h1⟩ := (hfx p).1 hpf
      exact h1
    have hr' := hRn _ hpfix r hr
    rw [tvP_inv] at hr'
    have h1 := hu _ hr'
    simp only [Equiv.Perm.mul_apply] at h1
    have h2 := congrArg (tvP ⟨p, hp⟩) h1
    rw [← Equiv.Perm.mul_apply, tvP_mul_self] at h2
    simpa using h2
  obtain ⟨q₀, hq₀, horb⟩ := horb
  have hq₀' := lt_of_mem_trFixL hq₀
  have hiff := horb (fun n => ∀ hn : n < 1953, (P ⟨q₀, hq₀'⟩ ↔ P ⟨n, hn⟩)) (fun _ => Iff.rfl)
    (fun q hq u hu hQ hn => by
      have hq' := lt_of_mem_trFixL hq
      have hu' := lt_of_mem_trFixL hu
      have hap : tvP ⟨q, hq'⟩ ⟨u, hu'⟩ = ⟨tvImg q u, hn⟩ := Fin.ext (tvP_apply _ _)
      have hback : tvP ⟨q, hq'⟩ ⟨tvImg q u, hn⟩ = ⟨u, hu'⟩ := by
        rw [← hap, ← Equiv.Perm.mul_apply, tvP_mul_self]
        rfl
      rw [hQ hu']
      constructor
      · intro h1
        rw [← hap]
        exact hP _ hq hq' _ h1
      · intro h1
        rw [← hback]
        exact hP _ hq hq' _ h1)
  have hP0 : P ⟨q₀, hq₀'⟩ := by
    have h1 := hiff x₀.1.val ((hfx _).2 ⟨x₀.1.2, x₀.2⟩) x₀.1.2
    exact h1.2 (fun r hr => congrArg Subtype.val (hx₀ ⟨r, hr⟩))
  rw [eq_bot_iff]
  intro r hr
  rw [mem_bot]
  refine eq_one_of_fix6 (hRT hr) hb6l (fun x hx => ?_) hind
  obtain ⟨hx', hfix'⟩ := (hfx x).1 (hb6 x hx)
  exact ⟨hx', ((hiff x (hb6 x hx) hx').1 hP0) r hr⟩

end CFSG.GF2Type.SmithTypeE.L6
