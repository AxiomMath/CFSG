module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Brg
public import CFSG.Permutation.AlternatingAutomorphism.JohnsonGraphIso
public import CFSG.ClassicalInvolution.Q3.AE.Twins

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Mdl117

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.AlternatingAutomorphism

variable {n : ℕ}

abbrev GBar (n : ℕ) : Subgroup (AEQ n) := (aeSub n).map (mkQ n)

@[expose] def MemberPerm (β : MulAut ↥(GBar n)) : Prop :=
  ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
    ∃ (α' : Finset (Fin n)) (h' : α'.card = 4) (b' : Bool),
      ((memBar α h b).subgroupOf (GBar n)).map β.toMonoidHom = (memBar α' h' b').subgroupOf (GBar n)

theorem memBar_le_GBar (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    memBar α h b ≤ GBar n := by
  apply Subgroup.map_mono
  cases b
  · exact memKStar_le_aeSub _
  · exact memK_le_aeSub _

theorem zBar_mem_GBar (α : Finset (Fin n)) (h : α.card = 4) : zBar α h ∈ GBar n :=
  memBar_le_GBar α h true (zBar_mem_memBar α h true)

noncomputable abbrev zBarG (α : Finset (Fin n)) (h : α.card = 4) : ↥(GBar n) :=
  ⟨zBar α h, zBar_mem_GBar α h⟩

theorem zBar_congr {α α' : Finset (Fin n)} {h : α.card = 4} {h' : α'.card = 4} (he : α = α') :
    zBar α h = zBar α' h' := by
  subst he
  rfl

section Map

variable {β : MulAut ↥(GBar n)} {α α' : Finset (Fin n)} {h : α.card = 4} {h' : α'.card = 4}
  {b b' : Bool}

theorem mem_of_map_eq
    (he : ((memBar α h b).subgroupOf (GBar n)).map β.toMonoidHom =
      (memBar α' h' b').subgroupOf (GBar n)) {g : ↥(GBar n)} (hg : (g : AEQ n) ∈ memBar α h b) :
    ((β g : ↥(GBar n)) : AEQ n) ∈ memBar α' h' b' := by
  have hm : β g ∈ ((memBar α h b).subgroupOf (GBar n)).map β.toMonoidHom :=
    ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  rw [he] at hm
  exact Subgroup.mem_subgroupOf.mp hm

theorem exists_of_map_eq
    (he : ((memBar α h b).subgroupOf (GBar n)).map β.toMonoidHom =
      (memBar α' h' b').subgroupOf (GBar n)) {x : AEQ n} (hx : x ∈ memBar α' h' b') :
    ∃ g : ↥(GBar n), (g : AEQ n) ∈ memBar α h b ∧ ((β g : ↥(GBar n)) : AEQ n) = x := by
  have hxG : x ∈ GBar n := memBar_le_GBar α' h' b' hx
  have hm : (⟨x, hxG⟩ : ↥(GBar n)) ∈ (memBar α' h' b').subgroupOf (GBar n) :=
    Subgroup.mem_subgroupOf.mpr hx
  rw [← he] at hm
  obtain ⟨g, hg, hgx⟩ := hm
  exact ⟨g, Subgroup.mem_subgroupOf.mp hg, congrArg Subtype.val hgx⟩

theorem beta_zBar_of_map_eq (hn : 5 ≤ n)
    (he : ((memBar α h b).subgroupOf (GBar n)).map β.toMonoidHom =
      (memBar α' h' b').subgroupOf (GBar n)) :
    ((β (zBarG α h) : ↥(GBar n)) : AEQ n) = zBar α' h' := by
  have hmem := mem_of_map_eq he (g := zBarG α h) (zBar_mem_memBar α h b)
  have h2 : ((β (zBarG α h) : ↥(GBar n)) : AEQ n) * ((β (zBarG α h) : ↥(GBar n)) : AEQ n) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul]
    have hz : zBarG α h * zBarG α h = 1 := Subtype.ext (zBar_mul_self α h)
    rw [hz, map_one]
    rfl
  rcases eq_of_mem_memBar_mul_self hn hmem h2 with h1 | h1
  · exfalso
    have h3 : β (zBarG α h) = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h3
    exact zBar_ne_one hn α h (congrArg Subtype.val h3)
  · exact h1

end Map

abbrev Q4 (n : ℕ) := {s : Finset (Fin n) // s.card = 4}

theorem exists_zBar (hn : 5 ≤ n) {β : MulAut ↥(GBar n)} (hβ : MemberPerm β) (s : Q4 n) :
    ∃ t : Q4 n, ((β (zBarG s.1 s.2) : ↥(GBar n)) : AEQ n) = zBar t.1 t.2 := by
  obtain ⟨α', h', b', he⟩ := hβ s.1 s.2 true
  exact ⟨⟨α', h'⟩, beta_zBar_of_map_eq hn he⟩

theorem orderOf_beta_mul {β : MulAut ↥(GBar n)} (g g' : ↥(GBar n)) :
    orderOf (((β g : ↥(GBar n)) : AEQ n) * ((β g' : ↥(GBar n)) : AEQ n)) =
      orderOf ((g : AEQ n) * (g' : AEQ n)) := by
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ← map_mul,
    MulEquiv.orderOf_eq]

theorem exists_perm_of_memberPerm (hn5 : 5 ≤ n) (hn8 : n ≠ 8) (hA : AdjInv n)
    {β : MulAut ↥(GBar n)} (hβ : MemberPerm β) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (α : Finset (Fin n)) (h : α.card = 4),
      ((β (zBarG α h) : ↥(GBar n)) : AEQ n) =
        zBar (α.map σ.toEmbedding) (by rw [Finset.card_map]; exact h) := by
  choose p hp using fun s : Q4 n => exists_zBar hn5 hβ s
  have hmem : ∀ (s : Q4 n) (b : Bool), ∃ b' : Bool,
      ((memBar s.1 s.2 b).subgroupOf (GBar n)).map β.toMonoidHom =
        (memBar (p s).1 (p s).2 b').subgroupOf (GBar n) := by
    intro s b
    obtain ⟨α', h', b', he⟩ := hβ s.1 s.2 b
    have hα : α' = (p s).1 := by
      have h1 := beta_zBar_of_map_eq hn5 he
      rw [hp s] at h1
      exact (eq_of_zBar_eq hn8 h1).symm
    subst hα
    exact ⟨b', he⟩
  have himg : ∀ (s : Q4 n) (c : Bool), ∃ b : Bool,
      ((memBar s.1 s.2 b).subgroupOf (GBar n)).map β.toMonoidHom =
        (memBar (p s).1 (p s).2 c).subgroupOf (GBar n) := by
    intro s c
    obtain ⟨c₁, hc₁⟩ := hmem s true
    obtain ⟨c₂, hc₂⟩ := hmem s false
    have hne : c₁ ≠ c₂ := by
      rintro rfl
      rw [← hc₂] at hc₁
      have h1 := Subgroup.map_injective β.injective hc₁
      rw [Subgroup.subgroupOf_inj, inf_of_le_left (memBar_le_GBar _ _ _),
        inf_of_le_left (memBar_le_GBar _ _ _)] at h1
      exact memBar_true_ne_false hn5 s.1 s.2 h1
    by_cases hc : c = c₁
    · exact ⟨true, hc ▸ hc₁⟩
    · refine ⟨false, ?_⟩
      have : c = c₂ := by
        cases c <;> cases c₁ <;> cases c₂ <;> simp_all
      exact this ▸ hc₂
  have hinj : Function.Injective p := by
    intro s t hst
    have h1 : ((β (zBarG s.1 s.2) : ↥(GBar n)) : AEQ n) =
        ((β (zBarG t.1 t.2) : ↥(GBar n)) : AEQ n) := by
      rw [hp s, hp t, hst]
    have h2 := β.injective (Subtype.ext h1)
    exact Subtype.ext (eq_of_zBar_eq hn8 (congrArg Subtype.val h2))
  have hbij : Function.Bijective p := Finite.injective_iff_bijective.mp hinj
  have hadj : ∀ s t : Q4 n, ((p s).1 ∩ (p t).1).card = 3 ↔ (s.1 ∩ t.1).card = 3 := by
    intro s t
    constructor
    · intro h3
      obtain ⟨c, c', x, hx, x', hx', h5⟩ := (hA (p s).1 (p s).2 (p t).1 (p t).2).mp h3
      obtain ⟨b, hb⟩ := himg s c
      obtain ⟨b', hb'⟩ := himg t c'
      obtain ⟨g, hg, rfl⟩ := exists_of_map_eq hb hx
      obtain ⟨g', hg', rfl⟩ := exists_of_map_eq hb' hx'
      exact (hA s.1 s.2 t.1 t.2).mpr ⟨b, b', g, hg, g', hg', by rw [← orderOf_beta_mul]; exact h5⟩
    · intro h3
      obtain ⟨b, b', k, hk, k', hk', h5⟩ := (hA s.1 s.2 t.1 t.2).mp h3
      obtain ⟨c, hc⟩ := hmem s b
      obtain ⟨c', hc'⟩ := hmem t b'
      let g : ↥(GBar n) := ⟨k, memBar_le_GBar _ _ _ hk⟩
      let g' : ↥(GBar n) := ⟨k', memBar_le_GBar _ _ _ hk'⟩
      refine (hA (p s).1 (p s).2 (p t).1 (p t).2).mpr ⟨c, c', _, mem_of_map_eq hc (g := g) hk, _,
        mem_of_map_eq hc' (g := g') hk', ?_⟩
      rw [orderOf_beta_mul]
      exact h5
  let P : Q4 n ≃ Q4 n := Equiv.ofBijective p hbij
  let F : johnsonGraph (Fin n) 4 ≃g johnsonGraph (Fin n) 4 :=
    { toEquiv := P
      map_rel_iff' := by
        intro s t
        simp only [johnsonGraph.adj_iff]
        have := hadj s t
        change ((p s).1 ∩ (p t).1).card + 1 = 4 ↔ (s.1 ∩ t.1).card + 1 = 4
        omega }
  obtain ⟨σ, hσ⟩ := johnsonGraph.exists_perm_of_iso (by rw [Fintype.card_fin]; omega) F
  refine ⟨σ, fun α h => ?_⟩
  rw [hp ⟨α, h⟩]
  exact zBar_congr (hσ ⟨α, h⟩)

end CFSG.ClassicalInvolution.Q3.TL4.Mdl117
