module

public import CFSG.CGT.PushingUpLit.SYMB.FiveNonSurj

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7 Equiv
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {V₁ E : Subgroup Γ} {a b c d : Fin 5}

theorem Wset_bot_pos (hV : V1Iso S V₁) (hp : Pts G T φ a b c d) :
    0 < (Wset G T φ ⊥).ncard := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
  have hmem : Up φ ψ V₁ A₀ ⊥ ∈ Wset G T φ ⊥ :=
    Up_mem_Wset hV hp (show A₀ ∈ Wset G T φ (imgG G φ A₀) from ⟨hA₀, rfl⟩)
      (member_good hV hp hA₀) Good.bot bot_le
  exact (Set.ncard_pos (Set.toFinite _)).2 ⟨_, hmem⟩

theorem ncard_Wset_swap_eq (hc : FiveCase S E) (hker : kerG G φ ≤ T) (hp : Pts G T φ a b c d) :
    (Wset G T φ (Subgroup.zpowers (swap a b))).ncard =
      (Wset G T φ (Subgroup.zpowers (swap c d))).ncard := by
  obtain ⟨g, hgE, hgT, hgφ⟩ := exists_g hc hker hp
  obtain ⟨hγ1, -, -, -⟩ := gamma_facts a b c d hp.hab hp.hcd hp.hac hp.had hp.hbc hp.hbd
  exact ncard_Wset_eq hgT (hc.join.le hgE) (by rw [hgφ, conjSub_zpowers', hγ1])

theorem strict_swap (hc : FiveCase S E) (hker : kerG G φ ≤ T) (hV : V1Iso S ⁅V, E⁆)
    (hp : Pts G T φ a b c d) {z : Γ} (hz2 : z * z = 1) (hzG : ∀ g ∈ G, g * z = z * g)
    (hzV : z ∉ ⁅V, E⁆)
    (hsq : ∀ (e : Γ) (he : e ∈ E), (φ ⟨e, hc.join.le he⟩) ^ 2 = 1 → φ ⟨e, hc.join.le he⟩ ≠ 1 →
      z⁻¹ * e ^ 2 ∈ ⁅V, E⁆)
    {x : Γ} (hxG : x ∈ G) (hφx : φ ⟨x, hxG⟩ = swap a b) :
    (memSet T x).ncard <
      (Wset G T φ ⊥).ncard + (Wset G T φ (Subgroup.zpowers (swap c d))).ncard := by
  classical
  have hbot := Wset_bot_pos hV hp
  have hsub := memSet_subset_union hV hp hxG hφx
  have hU : (memSet T x).ncard ≤
      (Wx G T φ (Subgroup.zpowers (swap a b)) x).ncard +
        (Wx G T φ (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) x).ncard :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  have hn₁ := ncard_Wx_swap_le hV hp hxG hφx
  by_cases hY : (Wx G T φ (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) x).Nonempty
  · obtain ⟨A₀, hA₀⟩ := hY
    have hx2 : x * x = 1 := elemAb_sq hA₀.1.1.2.1 hA₀.2
    obtain ⟨A', hA'W, havoid⟩ := exists_avoid hc hker hV hp hz2 hzG hzV hsq hxG hx2 hφx hA₀
    have h2 := ncard_Wx_add_one_le hV hp Good.Y Good.t₂ le_sup_right hxG
      (by
        intro p hp'
        rw [hφx]
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp'
        exact ((show Commute (swap c d) (swap a b) from hp.comm.symm).zpow_left j).eq)
      (by rw [hφx, sup_comm]) hA'W havoid
    omega
  · have hY0 : (Wx G T φ (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) x).ncard =
        0 := by
      rw [Set.not_nonempty_iff_eq_empty.1 hY]
      exact Set.ncard_empty _
    by_cases hmem : (memSet T x).Nonempty
    · obtain ⟨A, hA⟩ := hmem
      rcases hsub hA with hA1 | hA2
      · have h1 : 0 < (Wset G T φ (Subgroup.zpowers (swap a b))).ncard :=
          (Set.ncard_pos (Set.toFinite _)).2 ⟨A, hA1.1⟩
        have heq := ncard_Wset_swap_eq hc hker hp
        omega
      · exact absurd ⟨A, hA2⟩ hY
    · have h0 : (memSet T x).ncard = 0 := by
        rw [Set.not_nonempty_iff_eq_empty.1 hmem]
        exact Set.ncard_empty _
      omega

theorem strict_prod (hV : V1Iso S V₁) (hp : Pts G T φ a b c d) {x : Γ} (hxG : x ∈ G)
    (hφx : φ ⟨x, hxG⟩ = swap a b * swap c d) :
    (memSet T x).ncard <
      (Wset G T φ ⊥).ncard + (Wset G T φ (Subgroup.zpowers (swap a b))).ncard := by
  have h1 := ncard_memSet_prod_le hV hp hxG hφx
  have h2 := Wset_bot_pos hV hp
  omega

theorem strict_B (hc : FiveCase S E) (hker : kerG G φ ≤ T) (hV : V1Iso S ⁅V, E⁆)
    (hp : Pts G T φ a b c d) {z : Γ} (hz2 : z * z = 1) (hzG : ∀ g ∈ G, g * z = z * g)
    (hzV : z ∉ ⁅V, E⁆)
    (hsq : ∀ (e : Γ) (he : e ∈ E), (φ ⟨e, hc.join.le he⟩) ^ 2 = 1 → φ ⟨e, hc.join.le he⟩ ≠ 1 →
      z⁻¹ * e ^ 2 ∈ ⁅V, E⁆)
    {x : Γ} (hxB : x ∈ baum T) (hxG : x ∈ G) (hx1 : φ ⟨x, hxG⟩ ≠ 1) :
    (memSet T x).ncard <
      (Wset G T φ ⊥).ncard + (Wset G T φ (Subgroup.zpowers (swap a b))).ncard := by
  have hxY : φ ⟨x, hxG⟩ ∈ Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d) := by
    rw [← hp.hY]
    exact mem_imgG.2 ⟨x, hxG, hxB, rfl⟩
  rcases (mem_zpowers_sup_pair (swap_mul_self a b) (swap_mul_self c d) hp.comm).1 hxY with
    h | h | h | h
  · exact absurd h hx1
  · have := strict_swap hc hker hV hp hz2 hzG hzV hsq hxG h
    rwa [← ncard_Wset_swap_eq hc hker hp] at this
  · exact strict_swap hc hker hV hp.symm hz2 hzG hzV hsq hxG h
  · exact strict_prod hV hp hxG h

theorem lower_t₁ (hV : V1Iso S V₁) (hp : Pts G T φ a b c d) {v : Γ}
    (hv : v ∈ Cfix ψ V₁ (Subgroup.zpowers (swap a b))) :
    (Wset G T φ ⊥).ncard + (Wset G T φ (Subgroup.zpowers (swap a b))).ncard ≤
      (memSet T v).ncard := by
  refine ncard_le_memSet hV ?_ hv
  intro h0
  have : swap a b ∈ (⊥ : Subgroup (Equiv.Perm (Fin 5))) := h0 ▸ Subgroup.mem_zpowers _
  exact swap_ne_one hp.hab (Subgroup.mem_bot.1 this)

theorem lower_t₂ (hc : FiveCase S E) (hker : kerG G φ ≤ T) (hV : V1Iso S V₁)
    (hp : Pts G T φ a b c d) {v : Γ} (hv : v ∈ Cfix ψ V₁ (Subgroup.zpowers (swap c d))) :
    (Wset G T φ ⊥).ncard + (Wset G T φ (Subgroup.zpowers (swap a b))).ncard ≤
      (memSet T v).ncard := by
  rw [ncard_Wset_swap_eq hc hker hp]
  refine ncard_le_memSet hV ?_ hv
  intro h0
  have : swap c d ∈ (⊥ : Subgroup (Equiv.Perm (Fin 5))) := h0 ▸ Subgroup.mem_zpowers _
  exact swap_ne_one hp.hcd (Subgroup.mem_bot.1 this)

end CFSG.CGT.PushingUpLit.SYMB
