module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsBasic
public import CFSG.CGT.PushingUpLit.CGT6.Diag.Defs
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Main

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Cons

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

@[expose] noncomputable def resW (K : Subgroup (MulAut V)) (W : Subgroup V) (hW : GInv K W) :
    ↥K →* MulAut ↥W where
  toFun k := restrictAut (k : MulAut V) W (hW k k.2)
    (fun a ha => hW (k : MulAut V)⁻¹ (K.inv_mem k.2) a ha)
  map_one' := by
    ext h
    rfl
  map_mul' x y := by
    ext h
    rfl

theorem resW_apply (K : Subgroup (MulAut V)) (W : Subgroup V) (hW : GInv K W) (k : ↥K)
    (w : ↥W) : ((resW K W hW k w : ↥W) : V) = (k : MulAut V) (w : V) := rfl

theorem mem_ker_resW {K : Subgroup (MulAut V)} {W : Subgroup V} {hW : GInv K W} {k : ↥K} :
    k ∈ (resW K W hW).ker ↔ ∀ w ∈ W, (k : MulAut V) w = w := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h w hw
    have := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : V)) h
    simpa [resW_apply] using this
  · intro h
    ext w
    simpa [resW_apply] using h w w.2

theorem resW_irreducible {K : Subgroup (MulAut V)} {W : Subgroup V} (hW : DiagMinInv K W) :
    ∀ A : Subgroup ↥W, GInv (resW K W hW.2.1).range A → A = ⊥ ∨ A = ⊤ := by
  intro A hA
  have hB : GInv K (A.map W.subtype) := by
    rintro g hg _ ⟨a, ha, rfl⟩
    exact ⟨resW K W hW.2.1 ⟨g, hg⟩ a, hA _ ⟨⟨g, hg⟩, rfl⟩ a ha, rfl⟩
  rcases hW.2.2 _ hB (Subgroup.map_subtype_le A) with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective A W.subtype_injective).mp h
  · right
    rw [eq_top_iff]
    intro w _
    have : (w : V) ∈ A.map W.subtype := by rw [h]; exact w.2
    obtain ⟨a, ha, haw⟩ := this
    have : a = w := Subtype.ext haw
    rwa [← this]

theorem center_eq_bot_of_equiv_sl2 {G : Type*} [Group G] {f : ℕ}
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq f)) : Subgroup.center G = ⊥ := by
  have h1 : (Subgroup.center G).map e.toMonoidHom =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (Fq f)) := Subgroup.map_center_eq e
  rw [sl2_center_eq_bot] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

theorem two_pow_le_card_of_minInv [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {K : Subgroup (MulAut V)}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hfix : fixV K = ⊥) {f : ℕ} (hf : 1 ≤ f)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq f)) {W : Subgroup V} (hW : DiagMinInv K W) :
    2 ^ (2 * f) ≤ Nat.card ↥W := by
  have hcen : Subgroup.center ↥K = ⊥ := center_eq_bot_of_equiv_sl2 e
  set ρ := resW K W hW.2.1 with hρ
  have hker : ρ.ker = ⊥ := by
    rcases normal_le_center_or_eq_top hq ρ.ker with h1 | h1
    · rwa [hcen, le_bot_iff] at h1
    · exfalso
      apply hW.1
      rw [eq_bot_iff, ← hfix]
      intro w hw k hk
      have : (⟨k, hk⟩ : ↥K) ∈ ρ.ker := by rw [h1]; trivial
      exact mem_ker_resW.mp this w hw
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hker
  have hnt : ∃ g ∈ ρ.range, ∃ v : ↥W, g v ≠ v := by
    obtain ⟨k, hk, w, hw, hne⟩ := exists_move_of_fixV hfix hW.1
    exact ⟨ρ ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩, ⟨w, hw⟩, fun h1 => hne (congrArg Subtype.val h1)⟩
  exact l2_two_pow_two_mul_le_card f hf ↥W (fun v => Subtype.ext (hV v)) ρ.range
    ⟨(MonoidHom.ofInjective hinj).symm.trans e⟩ (resW_irreducible hW) hnt

theorem apply_eq_of_card_le_four [Finite V] {K : Subgroup (MulAut V)} (hK : Group.IsPerfect ↥K)
    {W : Subgroup V} (hW : GInv K W) (hc : Nat.card ↥W ≤ 4) :
    ∀ k ∈ K, ∀ w ∈ W, k w = w := by
  have hsolv : Group.IsSolvable (Equiv.Perm ↥W) := Equiv.Perm.isSolvable hc
  let π : ↥K →* Equiv.Perm ↥W := (MulAut.toPerm ↥W).comp (resW K W hW)
  have hperf : Group.IsPerfect π.range := Group.IsPerfect.range π
  have hsub : Subsingleton ↥π.range := by
    by_contra hns
    have : Nontrivial ↥π.range := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable ↥π.range inferInstance
  intro k hk w hw
  have h1 : π ⟨k, hk⟩ = 1 := by
    have := Subsingleton.elim (⟨π ⟨k, hk⟩, ⟨k, hk⟩, rfl⟩ : ↥π.range) 1
    exact congrArg Subtype.val this
  have h2 : ((π ⟨k, hk⟩ ⟨w, hw⟩ : ↥W) : V) = w :=
    congrArg (fun σ : Equiv.Perm ↥W => ((σ ⟨w, hw⟩ : ↥W) : V)) h1
  exact h2

end CFSG.CGT.PushingUpLit.CGT6.Diag.Cons
