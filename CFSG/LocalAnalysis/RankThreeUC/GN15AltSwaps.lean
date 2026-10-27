module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltFusion
import CFSG.CGT.PushingUpLit.BHSSym.PermSylow
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModPair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThree.PartTwo
open Equiv Equiv.Perm
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)} {n : ℕ}
  {g : ↥L →* alternatingGroup (Fin n)}

namespace GNAltModData

variable (S : GNAltModData T L g)

theorem eq_of_swap_mem_Q {x y z : Fin n} (hxy : x ≠ y) (hxz : x ≠ z)
    (h1 : swap x y ∈ S.Q) (h2 : swap x z ∈ S.Q) : y = z :=
  CFSG.CGT.PushingUpLit.BHSSym.eq_of_swap_mem S.sylow.1 hxy hxz h1 h2

theorem swap_conj_mem_Q {a b a' b' : Fin n} (hab : a ≠ b)
    (hab' : a' ≠ b') (haa' : a ≠ a') (hab'' : a ≠ b') (hba' : b ≠ a') (hbb' : b ≠ b')
    (h1 : swap a b ∈ S.Q) (h2 : swap a' b' ∈ S.Q) :
    ∀ x y : Fin n, x ≠ y → swap x y ∈ S.Q →
      swap ((swap a a' * swap b b') x) ((swap a a' * swap b b') y) ∈ S.Q := by
  intro x y hxy hQ
  have hγa : (swap a a' * swap b b') a = a' := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab hab'', swap_apply_left]
  have hγb : (swap a a' * swap b b') b = b' := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hab''.symm hab'.symm]
  have hγa' : (swap a a' * swap b b') a' = a := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hba'.symm hab', swap_apply_right]
  have hγb' : (swap a a' * swap b b') b' = b := by
    rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hab.symm hba']
  have hfix : ∀ z : Fin n, z ≠ a → z ≠ b → z ≠ a' → z ≠ b' → (swap a a' * swap b b') z = z := by
    intro z hza hzb hza' hzb'
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hzb hzb', swap_apply_of_ne_of_ne hza hza']
  have hpa : ∀ v : Fin n, a ≠ v → swap a v ∈ S.Q → v = b := fun v hv hQ' =>
    (S.eq_of_swap_mem_Q hab hv h1 hQ').symm
  have hpb : ∀ v : Fin n, b ≠ v → swap b v ∈ S.Q → v = a := fun v hv hQ' =>
    (S.eq_of_swap_mem_Q hab.symm hv (by rwa [swap_comm]) hQ').symm
  have hpa' : ∀ v : Fin n, a' ≠ v → swap a' v ∈ S.Q → v = b' := fun v hv hQ' =>
    (S.eq_of_swap_mem_Q hab' hv h2 hQ').symm
  have hpb' : ∀ v : Fin n, b' ≠ v → swap b' v ∈ S.Q → v = a' := fun v hv hQ' =>
    (S.eq_of_swap_mem_Q hab'.symm hv (by rwa [swap_comm]) hQ').symm
  by_cases hxa : x = a
  · subst hxa
    have hyb := hpa y hxy hQ
    subst hyb
    rw [hγa, hγb]; exact h2
  by_cases hxb : x = b
  · subst hxb
    have hya := hpb y hxy hQ
    subst hya
    rw [hγb, hγa, swap_comm]; exact h2
  by_cases hxa' : x = a'
  · subst hxa'
    have hyb := hpa' y hxy hQ
    subst hyb
    rw [hγa', hγb']; exact h1
  by_cases hxb' : x = b'
  · subst hxb'
    have hya := hpb' y hxy hQ
    subst hya
    rw [hγb', hγa', swap_comm]; exact h1
  have hQ' : swap y x ∈ S.Q := by rwa [swap_comm]
  have hya : y ≠ a := fun h => by
    subst h
    exact hxb (hpa x hxy.symm hQ')
  have hyb : y ≠ b := fun h => by
    subst h
    exact hxa (hpb x hxy.symm hQ')
  have hya' : y ≠ a' := fun h => by
    subst h
    exact hxb' (hpa' x hxy.symm hQ')
  have hyb' : y ≠ b' := fun h => by
    subst h
    exact hxa' (hpb' x hxy.symm hQ')
  rw [hfix x hxa hxb hxa' hxb', hfix y hya hyb hya' hyb']
  exact hQ

theorem conj_J_le_Q {γ : Perm (Fin n)}
    (h : ∀ x y : Fin n, x ≠ y → swap x y ∈ S.Q → swap (γ x) (γ y) ∈ S.Q) :
    ∀ j ∈ S.J, γ * j * γ⁻¹ ∈ S.Q := by
  obtain ⟨T', -, hT's, -, hT'J⟩ := S.J_swaps
  have hJ : S.J = Subgroup.closure T' := hT'J
  have hle : S.J ≤ S.Q.comap (MulAut.conj γ).toMonoidHom := by
    rw [hJ, Subgroup.closure_le]
    intro t ht
    obtain ⟨x, y, hxy, rfl⟩ := hT's t ht
    have htQ : swap x y ∈ S.Q := S.J_le_Q (by rw [hJ]; exact Subgroup.subset_closure ht)
    show γ * swap x y * γ⁻¹ ∈ S.Q
    rw [← swap_apply_apply]
    exact h x y hxy htQ
  intro j hj
  exact hle hj

theorem exists_lift_of_mem_alternatingGroup {γ : Perm (Fin n)}
    (hγ : γ ∈ alternatingGroup (Fin n)) :
    ∃ (l : X) (hl : toStar T l ∈ L), S.ρ ⟨l, Subgroup.le_normalizer hl⟩ = γ := by
  obtain ⟨ℓ, hℓ⟩ := S.g_bij.2 ⟨γ, hγ⟩
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (ℓ : X ⧸ gnC T)
  have hlL : toStar T l ∈ L := by
    rw [show toStar T l = (ℓ : X ⧸ gnC T) from hl]
    exact ℓ.2
  refine ⟨l, hlL, ?_⟩
  have h1 := S.ρ_pre ⟨l, hlL⟩ hlL
  have h2 : (⟨toStar T l, hlL⟩ : ↥L) = ℓ := Subtype.ext hl
  rw [h2] at h1
  rw [show S.ρ ⟨l, Subgroup.le_normalizer hlL⟩ = (g ℓ : Perm (Fin n)) from h1]
  exact congrArg Subtype.val hℓ

theorem jAllSwaps_of_gnSetting (hX : GNSetting X T) (hL : IsComponentOf L ⊤) : S.JAllSwaps := by
  classical
  intro s hsQ hsw
  obtain ⟨T', ⟨s₀, hs₀⟩, hT's, -, hT'J⟩ := S.J_swaps
  have hJ : S.J = Subgroup.closure T' := hT'J
  have hs₀J : s₀ ∈ S.J := by rw [hJ]; exact Subgroup.subset_closure hs₀
  obtain ⟨a, b, hab, rfl⟩ := hT's s₀ hs₀
  obtain ⟨a', b', hab', rfl⟩ := hsw
  have hs₀Q : swap a b ∈ S.Q := S.J_le_Q hs₀J
  by_cases hdisj : a ≠ a' ∧ a ≠ b' ∧ b ≠ a' ∧ b ≠ b'
  · obtain ⟨haa', hab'', hba', hbb'⟩ := hdisj
    have hγA : swap a a' * swap b b' ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup, Perm.sign_mul, sign_swap haa', sign_swap hbb']
      decide
    obtain ⟨l, hl, hρl⟩ := S.exists_lift_of_mem_alternatingGroup hγA
    have hconj := S.swap_conj_mem_Q hab hab' haa' hab'' hba' hbb' hs₀Q hsQ
    have hJQ : ∀ j ∈ S.J, S.ρ ⟨l, Subgroup.le_normalizer hl⟩ * j *
        (S.ρ ⟨l, Subgroup.le_normalizer hl⟩)⁻¹ ∈ S.Q := by
      rw [hρl]
      exact S.conj_J_le_Q hconj
    have := S.conj_mem_J_of_conj_J_le_Q hX hL hl hJQ _ hs₀J
    rw [hρl, ← swap_apply_apply] at this
    have hγa : (swap a a' * swap b b') a = a' := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab hab'', swap_apply_left]
    have hγb : (swap a a' * swap b b') b = b' := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hab''.symm hab'.symm]
    rwa [hγa, hγb] at this
  ·
    have hm := fun {x y z : Fin n} hxy hxz h1 h2 => S.eq_of_swap_mem_Q (x := x) (y := y) (z := z)
      hxy hxz h1 h2
    simp only [not_and_or, not_not] at hdisj
    rcases hdisj with h | h | h | h
    · subst h
      have := hm hab hab' hs₀Q hsQ
      subst this
      exact hs₀J
    · subst h
      have := hm hab hab'.symm hs₀Q (by rwa [swap_comm])
      subst this
      rw [swap_comm]
      exact hs₀J
    · subst h
      have := hm hab.symm hab' (by rwa [swap_comm]) hsQ
      subst this
      rw [swap_comm]
      exact hs₀J
    · subst h
      have := hm hab.symm hab'.symm (by rwa [swap_comm]) (by rwa [swap_comm])
      subst this
      exact hs₀J

theorem mem_normalizer_gnImg_baum_of_conj_J_le_Q (hX : GNSetting X T) (hL : IsComponentOf L ⊤)
    (hn : 4 ≤ n) {l : X} (hl : toStar T l ∈ L)
    (hJQ : ∀ j ∈ S.J, S.ρ ⟨l, Subgroup.le_normalizer hl⟩ * j *
      (S.ρ ⟨l, Subgroup.le_normalizer hl⟩)⁻¹ ∈ S.Q) :
    toStar T l ∈ Subgroup.normalizer (gnImg T (baum T) : Set (X ⧸ gnC T)) := by
  classical
  apply gnAlt_mem_normalizer_of_forall_conj_mem
  rintro _ ⟨x, hx, rfl⟩
  have hxN : x ∈ Subgroup.normalizer (gnPre T L : Set X) := S.baum_le hx
  obtain ⟨j, hj, hjρ⟩ := S.baum_map_mem_J hx
  have hjJ : (j : X) ∈ thompsonJ T := Subgroup.mem_subgroupOf.1 hj
  have hjB : (j : X) ∈ baum T := B6.thompsonJ_le_baum T hjJ
  have hdB : x * (j : X)⁻¹ ∈ baum T := (baum T).mul_mem hx ((baum T).inv_mem hjB)
  have hdN : x * (j : X)⁻¹ ∈ Subgroup.normalizer (gnPre T L : Set X) :=
    Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ j.2)
  have hρd : S.ρ ⟨x * (j : X)⁻¹, hdN⟩ = 1 := by
    have : (⟨x * (j : X)⁻¹, hdN⟩ : ↥(Subgroup.normalizer (gnPre T L : Set X))) =
        ⟨x, hxN⟩ * j⁻¹ := rfl
    rw [this, map_mul, map_inv, hjρ]
    simp
  have hdc := (S.ρ_eq_one_iff hn ⟨x * (j : X)⁻¹, hdN⟩).1 hρd
  have hcomm : toStar T l * toStar T (x * (j : X)⁻¹) = toStar T (x * (j : X)⁻¹) * toStar T l :=
    Subgroup.mem_centralizer_iff.1 hdc (toStar T l) hl
  have hmemc : l * (j : X) * l⁻¹ ∈ B6.conjSub l (thompsonJ T) := by
    rw [B6.mem_conjSub]
    have : l⁻¹ * (l * (j : X) * l⁻¹) * l = j := by group
    rw [this]
    exact hjJ
  have hconj : toStar T (l * (j : X) * l⁻¹) ∈ gnImg T (thompsonJ T) :=
    S.map_conjSub_thompsonJ_le hX hL hl hJQ ⟨_, hmemc, rfl⟩
  have hconjB : toStar T (l * (j : X) * l⁻¹) ∈ gnImg T (baum T) :=
    Subgroup.map_mono (B6.thompsonJ_le_baum T) hconj
  have hdB' : toStar T (x * (j : X)⁻¹) ∈ gnImg T (baum T) := Subgroup.mem_map_of_mem _ hdB
  have hx_eq : toStar T l * toStar T x * (toStar T l)⁻¹ =
      toStar T (x * (j : X)⁻¹) * toStar T (l * (j : X) * l⁻¹) := by
    have h1 : toStar T x = toStar T (x * (j : X)⁻¹) * toStar T (j : X) := by
      rw [← map_mul]; congr 1; group
    rw [h1]
    simp only [map_mul, map_inv] at hcomm ⊢
    calc toStar T l * (toStar T x * (toStar T (j : X))⁻¹ * toStar T (j : X)) * (toStar T l)⁻¹
        = (toStar T l * (toStar T x * (toStar T (j : X))⁻¹)) * toStar T (j : X) *
            (toStar T l)⁻¹ := by group
      _ = ((toStar T x * (toStar T (j : X))⁻¹) * toStar T l) * toStar T (j : X) *
            (toStar T l)⁻¹ := by rw [hcomm]
      _ = toStar T x * (toStar T (j : X))⁻¹ *
            (toStar T l * toStar T (j : X) * (toStar T l)⁻¹) := by group
  rw [hx_eq]
  exact (gnImg T (baum T)).mul_mem hdB' hconjB

theorem exists_mem_normalizer_baum_of_conj_J_le_Q (hX : GNSetting X T) (hL : IsComponentOf L ⊤)
    (hn : 4 ≤ n) {l : X} (hl : toStar T l ∈ L)
    (hJQ : ∀ j ∈ S.J, S.ρ ⟨l, Subgroup.le_normalizer hl⟩ * j *
      (S.ρ ⟨l, Subgroup.le_normalizer hl⟩)⁻¹ ∈ S.Q) :
    ∃ m ∈ Subgroup.normalizer (baum T : Set X), toStar T m = toStar T l := by
  have h := S.mem_normalizer_gnImg_baum_of_conj_J_le_Q hX hL hn hl hJQ
  rw [normalizer_gnImg_baum hX] at h
  obtain ⟨m, hm, hml⟩ := h
  exact ⟨m, hm, hml⟩

end GNAltModData

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

