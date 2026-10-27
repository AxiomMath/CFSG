module

public import CFSG.CGT.PushingUpLit.SYMB.FiveCount

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7 Equiv
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {V₁ : Subgroup Γ} {a b c d : Fin 5}

theorem Good.bot : Good a b c d ⊥ := Or.inl rfl

theorem Good.t₁ : Good a b c d (Subgroup.zpowers (swap a b)) := Or.inr (Or.inl rfl)

theorem Good.t₂ : Good a b c d (Subgroup.zpowers (swap c d)) := Or.inr (Or.inr (Or.inl rfl))

theorem Good.Y : Good a b c d (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) :=
  Or.inr (Or.inr (Or.inr rfl))

omit [Finite Γ] in
theorem Pts.comm {a b c d : Fin 5} (h : Pts G T φ a b c d) :
    swap a b * swap c d = swap c d * swap a b :=
  swap_comm_swap h.hac h.had h.hbc h.hbd

theorem ncard_memSet_prod_le (hV : V1Iso S V₁) (h : Pts G T φ a b c d) {x : Γ} (hxG : x ∈ G)
    (hφx : φ ⟨x, hxG⟩ = swap a b * swap c d) :
    (memSet T x).ncard ≤ (Wset G T φ (Subgroup.zpowers (swap a b))).ncard := by
  have hsub : memSet T x ⊆
      Wx G T φ (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) x := by
    rintro A ⟨hA, hxA⟩
    have hmem : swap a b * swap c d ∈ imgG G φ A := mem_imgG.2 ⟨x, hxG, hxA, hφx⟩
    rcases member_good hV h hA with hg | hg | hg | hg
    · exfalso
      rw [hg] at hmem
      exact swap_mul_swap_ne_one h.hab h.hac h.had (Subgroup.mem_bot.1 hmem)
    · exfalso
      rw [hg] at hmem
      exact prod_not_mem_ab h.hab h.hcd h.hac h.had hmem
    · exfalso
      rw [hg] at hmem
      exact prod_not_mem_cd h.hab h.hac h.had hmem
    · exact ⟨⟨hA, hg⟩, hxA⟩
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  refine ncard_Wx_le hV h Good.Y Good.t₁ le_sup_left hxG ?_ ?_
  · intro p hp
    rw [hφx]
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
    have c1 : Commute (swap a b ^ j) (swap a b) := (Commute.refl (swap a b)).zpow_left j
    have c2 : Commute (swap a b ^ j) (swap c d) :=
      (show Commute (swap a b) (swap c d) from h.comm).zpow_left j
    exact (c1.mul_right c2).eq
  · rw [hφx]
    refine sup_le le_sup_left (Subgroup.zpowers_le.2 ?_)
    have h1 : swap a b * (swap a b * swap c d) ∈
        Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap a b * swap c d) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    rwa [← mul_assoc, swap_mul_self, one_mul] at h1

theorem memSet_subset_union (hV : V1Iso S V₁) (h : Pts G T φ a b c d) {x : Γ} (hxG : x ∈ G)
    (hφx : φ ⟨x, hxG⟩ = swap a b) :
    memSet T x ⊆ Wx G T φ (Subgroup.zpowers (swap a b)) x ∪
      Wx G T φ (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) x := by
  rintro A ⟨hA, hxA⟩
  have hmem : swap a b ∈ imgG G φ A := mem_imgG.2 ⟨x, hxG, hxA, hφx⟩
  rcases member_good hV h hA with hg | hg | hg | hg
  · exfalso
    rw [hg] at hmem
    exact swap_ne_one h.hab (Subgroup.mem_bot.1 hmem)
  · exact Or.inl ⟨⟨hA, hg⟩, hxA⟩
  · exfalso
    rw [hg] at hmem
    exact swap_ab_not_mem_cd h.hab h.hac h.had hmem
  · exact Or.inr ⟨⟨hA, hg⟩, hxA⟩

theorem ncard_Wx_swap_le (hV : V1Iso S V₁) (h : Pts G T φ a b c d) {x : Γ} (hxG : x ∈ G)
    (hφx : φ ⟨x, hxG⟩ = swap a b) :
    (Wx G T φ (Subgroup.zpowers (swap a b)) x).ncard ≤ (Wset G T φ ⊥).ncard := by
  refine ncard_Wx_le hV h Good.t₁ Good.bot bot_le hxG ?_ ?_
  · intro p hp
    rw [Subgroup.mem_bot.1 hp, one_mul, mul_one]
  · rw [hφx, bot_sup_eq]

theorem ncard_Wx_add_one_le (hV : V1Iso S V₁) (h : Pts G T φ a b c d)
    {P₀ P : Subgroup (Equiv.Perm (Fin 5))} (hP₀ : Good a b c d P₀) (hP : Good a b c d P)
    (hle : P ≤ P₀) {x : Γ} (hxG : x ∈ G)
    (hPc : ∀ p ∈ P, p * φ ⟨x, hxG⟩ = φ ⟨x, hxG⟩ * p)
    (hP₀le : P₀ ≤ P ⊔ Subgroup.zpowers (φ ⟨x, hxG⟩)) {A' : Subgroup Γ}
    (hA' : A' ∈ Wset G T φ P) (havoid : ∀ A ∈ Wx G T φ P₀ x, Up φ ψ V₁ A P ≠ A') :
    (Wx G T φ P₀ x).ncard + 1 ≤ (Wset G T φ P).ncard := by
  have h1 : (Wx G T φ P₀ x).ncard ≤ (Wset G T φ P \ {A'}).ncard :=
    Set.ncard_le_ncard_of_injOn (Up φ ψ V₁ · P)
      (fun A hA => ⟨Up_mem_Wset hV h hA.1 hP₀ hP hle, fun he => havoid A hA he⟩)
      (fun A₁ hA₁ A₂ hA₂ he => eq_of_Up_eq hV hA₁.1.1 hA₂.1.1 hA₁.2 hA₂.2 hxG hPc
        (by rw [hA₁.1.2]; exact hP₀le) (by rw [hA₂.1.2]; exact hP₀le) he)
      (Set.toFinite _)
  have h2 : (Wset G T φ P \ {A'}).ncard = (Wset G T φ P).ncard - 1 :=
    Set.ncard_sdiff_singleton_of_mem hA'
  have h3 : 0 < (Wset G T φ P).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨A', hA'⟩
  omega

end CFSG.CGT.PushingUpLit.SYMB
