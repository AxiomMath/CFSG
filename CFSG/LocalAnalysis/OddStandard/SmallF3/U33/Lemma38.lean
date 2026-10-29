module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G V : Type*} [Group G] [Group V]

structure IsAutE16 (ρ : G →* MulAut V) : Prop where
  card_eq : Nat.card V = 16
  sq_eq_one : ∀ v : V, v ^ 2 = 1
  bijective : Function.Bijective ρ

@[expose] def actFixed (ρ : G →* MulAut V) (S : Set G) : Subgroup V where
  carrier := {v | ∀ g ∈ S, ρ g v = v}
  one_mem' := fun g _ => map_one (ρ g)
  mul_mem' := fun ha hb g hg => by rw [map_mul, ha g hg, hb g hg]
  inv_mem' := fun ha g hg => by rw [map_inv, ha g hg]

theorem isAutE16_id (h16 : Nat.card V = 16) (h2 : ∀ v : V, v ^ 2 = 1) :
    IsAutE16 (MonoidHom.id (MulAut V)) :=
  ⟨h16, h2, Function.bijective_id⟩

variable {ρ : G →* MulAut V}

section Core

variable {X : Type*} [Group X]

private theorem comm_of_sq_eq_one (h : ∀ v : X, v ^ 2 = 1) (x y : X) : x * y = y * x := by
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h x)
  have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h y)
  have hxy : (x * y)⁻¹ = x * y :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h (x * y))
  calc x * y = (x * y)⁻¹ := hxy.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx, hy]

private theorem core (hcard : Nat.card X = 16) (hsq : ∀ v : X, v ^ 2 = 1)
    (a b : MulAut X) (ha3 : a ^ 3 = 1) (hb2 : b ^ 2 = 1)
    (hrel : b * a * b⁻¹ = a ^ 2) (hfpf : ∀ v : X, a v = v → v = 1) :
    Nat.card {W : Subgroup X // Nat.card W = 4 ∧ (∀ w ∈ W, a w ∈ W) ∧
      (∀ w ∈ W, b w ∈ W)} = 3 := by
  classical
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have comm : ∀ x y : X, x * y = y * x := comm_of_sq_eq_one hsq
  letI : CommGroup X := { ‹Group X› with mul_comm := comm }
  have hba : b * a = a ^ 2 * b := by
    rw [← hrel, mul_assoc, inv_mul_cancel, mul_one]
  have hbb : ∀ x : X, b (b x) = x := by
    intro x
    have h := congrArg (fun f : MulAut X => f x) hb2
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply] at h
    exact h
  have haa : ∀ x : X, a (a (a x)) = x := by
    intro x
    have h := congrArg (fun f : MulAut X => f x) ha3
    have h3 : a ^ 3 = a ^ 2 * a := pow_succ a 2
    rw [h3] at h
    rw [MulAut.mul_apply, pow_two, MulAut.mul_apply, MulAut.one_apply] at h
    exact h
  have key : ∀ v : X, v ≠ 1 → v * a v * a (a v) = 1 := by
    intro v hv
    refine hfpf _ ?_
    rw [map_mul, map_mul, haa v]
    rw [mul_assoc, comm (a (a v)) v, ← mul_assoc, comm (a v) v]
  have ha2v : ∀ v : X, v ≠ 1 → a (a v) = v * a v := by
    intro v hv
    calc a (a v) = (v * a v)⁻¹ := eq_inv_of_mul_eq_one_right (key v hv)
      _ = v * a v :=
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq (v * a v))
  have hav_ne_v : ∀ v : X, v ≠ 1 → a v ≠ v := fun v hv h => hv (hfpf v h)
  have hav_ne_one : ∀ v : X, v ≠ 1 → a v ≠ 1 := by
    intro v hv h
    exact hv (a.injective (by rw [h, map_one]))
  have hva_ne_one : ∀ v : X, v ≠ 1 → v * a v ≠ 1 := by
    intro v hv h
    exact hav_ne_one v hv (a.injective (by rw [ha2v v hv, h, map_one]))
  have hva_ne_v : ∀ v : X, v ≠ 1 → v * a v ≠ v := by
    intro v hv h
    exact hav_ne_one v hv (mul_left_cancel (by rw [h, mul_one]))
  have hva_ne_av : ∀ v : X, v ≠ 1 → v * a v ≠ a v := by
    intro v hv h
    exact hv (mul_right_cancel (by rw [h, one_mul]))
  have ha2v_ne_v : ∀ v : X, v ≠ 1 → a (a v) ≠ v := by
    intro v hv h
    exact hva_ne_v v hv ((ha2v v hv).symm.trans h)
  have ha2v_ne_av : ∀ v : X, v ≠ 1 → a (a v) ≠ a v := by
    intro v hv h
    exact hva_ne_av v hv ((ha2v v hv).symm.trans h)
  have hpar : ∀ x : X, x ^ 2 = 1 → x ≠ 1 → ∀ m : ℤ, x ^ m = 1 ∨ x ^ m = x := by
    intro x hx2 hx1 m
    have horder : orderOf x = 2 := orderOf_eq_prime (by simpa [pow_two] using hx2) hx1
    have heq : x ^ m = x ^ (m % 2) := by
      rw [zpow_eq_zpow_iff_modEq, horder]
      exact (Int.mod_modEq m 2).symm
    rcases Int.emod_two_eq_zero_or_one m with h | h
    · left; rw [heq, h, zpow_zero]
    · right; rw [heq, h, zpow_one]
  have mem_W : ∀ v : X, v ≠ 1 → ∀ z : X,
      z ∈ Subgroup.closure ({v, a v} : Set X) ↔
        z = 1 ∨ z = v ∨ z = a v ∨ z = v * a v := by
    intro v hv z
    rw [Subgroup.mem_closure_pair]
    constructor
    · rintro ⟨m, n, rfl⟩
      rcases hpar v (hsq v) hv m with h | h <;>
        rcases hpar (a v) (hsq (a v)) (hav_ne_one v hv) n with h' | h'
      · exact Or.inl (by rw [h, h', one_mul])
      · exact Or.inr (Or.inr (Or.inl (by rw [h, h', one_mul])))
      · exact Or.inr (Or.inl (by rw [h, h', mul_one]))
      · exact Or.inr (Or.inr (Or.inr (by rw [h, h'])))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, 0, by simp⟩
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
      · exact ⟨1, 1, by simp⟩
  have hcardW : ∀ v : X, v ≠ 1 → Nat.card (Subgroup.closure ({v, a v} : Set X)) = 4 := by
    intro v hv
    have hset : (Subgroup.closure ({v, a v} : Set X) : Set X) =
        (↑({1, v, a v, v * a v} : Finset X) : Set X) := by
      ext z
      change z ∈ Subgroup.closure ({v, a v} : Set X) ↔
        z ∈ (↑({1, v, a v, v * a v} : Finset X) : Set X)
      rw [mem_W v hv z]
      simp [or_assoc]
    have hcard4 : ({1, v, a v, v * a v} : Finset X).card = 4 := by
      rw [Finset.card_eq_four]
      exact ⟨1, v, a v, v * a v, hv.symm, (hav_ne_one v hv).symm, (hva_ne_one v hv).symm,
        (hav_ne_v v hv).symm, (hva_ne_v v hv).symm, (hva_ne_av v hv).symm, rfl⟩
    change (Subgroup.closure ({v, a v} : Set X) : Set X).ncard = 4
    rw [hset, Set.ncard_coe_finset, hcard4]
  have a_inv_W : ∀ v : X, v ≠ 1 →
      ∀ w ∈ Subgroup.closure ({v, a v} : Set X),
        a w ∈ Subgroup.closure ({v, a v} : Set X) := by
    intro v hv w hw
    have hmap : Subgroup.map a.toMonoidHom (Subgroup.closure ({v, a v} : Set X)) =
        Subgroup.closure ({a v, a (a v)} : Set X) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z; simp
    have hle : Subgroup.closure ({a v, a (a v)} : Set X) ≤
        Subgroup.closure ({v, a v} : Set X) := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · rw [ha2v v hv]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    have hmem : a w ∈ Subgroup.map a.toMonoidHom (Subgroup.closure ({v, a v} : Set X)) :=
      ⟨w, hw, rfl⟩
    rw [hmap] at hmem
    exact hle hmem
  let φ : X →* X :=
    { toFun := fun v => v * b v
      map_one' := by rw [map_one, mul_one]
      map_mul' := fun x y => by
        rw [map_mul]
        exact Commute.mul_mul_mul_comm (comm y (b x)) x (b y) }
  let F : Subgroup X := φ.ker
  have mem_F : ∀ f : X, f ∈ F ↔ b f = f := by
    intro f
    change f * b f = 1 ↔ b f = f
    constructor
    · intro h
      rw [eq_inv_of_mul_eq_one_right h,
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq f)]
    · intro h
      rw [h]
      simpa [pow_two] using hsq f
  have range_le_F : φ.range ≤ F := by
    rintro x ⟨g, rfl⟩
    rw [mem_F]
    change b (g * b g) = g * b g
    rw [map_mul, hbb g, comm (b g) g]
  have hcardF_ge : 4 ≤ Nat.card F := by
    have hker := Subgroup.card_ker_mul_card_range φ
    have hle : Nat.card φ.range ≤ Nat.card F :=
      Nat.card_le_card_of_injective (Set.inclusion range_le_F) (Set.inclusion_injective range_le_F)
    have h16 : 16 ≤ Nat.card F ^ 2 := by
      calc 16 = Nat.card F * Nat.card φ.range := by rw [hker, hcard]
        _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul (le_refl _) hle
        _ = Nat.card F ^ 2 := (pow_two _).symm
    by_contra h
    push Not at h
    have hle3 : Nat.card F ≤ 3 := by omega
    have h9 : Nat.card F ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left hle3 2
    norm_num at h9
    omega
  have keyF : ∀ f f' : X, f ∈ F → f' ∈ F → f = a f' → f = 1 := by
    intro f f' hf hf' heq
    have hbf : b f = f := (mem_F f).mp hf
    have hbf' : b f' = f' := (mem_F f').mp hf'
    have hbaf' : b (a f') = a (a f') := by
      have h := congrArg (fun g : MulAut X => g f') hba
      simpa [MulAut.mul_apply, pow_two, hbf'] using h
    have h1 : f = a (a f') := by rw [← hbf, heq, hbaf']
    have h2 : a f' = a (a f') := heq.symm.trans h1
    have h3 : f' = a f' := a.injective h2
    have h4 : f' = 1 := hfpf f' h3.symm
    rw [heq, h4, map_one]
  have hpair_inj : Function.Injective (fun p : F × F => (p.1 : X) * a (p.2 : X)) := by
    rintro ⟨⟨f, hf⟩, ⟨f', hf'⟩⟩ ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩ h
    change f * a f' = g * a g' at h
    have hF1 : f * g⁻¹ ∈ F := F.mul_mem hf (F.inv_mem hg)
    have hF2 : g' * f'⁻¹ ∈ F := F.mul_mem hg' (F.inv_mem hf')
    have heq : f * g⁻¹ = a (g' * f'⁻¹) := by
      have h1 : f * g⁻¹ = a g' * (a f')⁻¹ := by
        rw [comm f g⁻¹]
        calc g⁻¹ * f = g⁻¹ * (f * a f') * (a f')⁻¹ := by group
          _ = g⁻¹ * (g * a g') * (a f')⁻¹ := by rw [h]
          _ = a g' * (a f')⁻¹ := by group
      have h2 : a (g' * f'⁻¹) = a g' * (a f')⁻¹ := by rw [map_mul, map_inv]
      exact h1.trans h2.symm
    have hf1 : f * g⁻¹ = 1 := keyF (f * g⁻¹) (g' * f'⁻¹) hF1 hF2 heq
    have hfg : f = g := by
      rw [mul_inv_eq_one] at hf1
      exact hf1
    have hf'g' : f' = g' := by
      have h' : a f' = a g' := by
        rw [hfg] at h
        exact mul_left_cancel h
      exact a.injective h'
    exact Prod.ext (Subtype.ext hfg) (Subtype.ext hf'g')
  have hcardF_le : Nat.card F ≤ 4 := by
    have hle : Nat.card (F × F) ≤ Nat.card X :=
      Nat.card_le_card_of_injective _ hpair_inj
    rw [Nat.card_prod, hcard] at hle
    by_contra h
    push Not at h
    have h5 : 5 ≤ Nat.card F := by omega
    have h25 : 25 ≤ Nat.card F * Nat.card F := by
      calc 25 = 5 * 5 := by norm_num
        _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul h5 h5
    omega
  have hcardF : Nat.card F = 4 := le_antisymm hcardF_le hcardF_ge
  have b_inv_W : ∀ f : X, f ∈ F → f ≠ 1 →
      ∀ w ∈ Subgroup.closure ({f, a f} : Set X),
        b w ∈ Subgroup.closure ({f, a f} : Set X) := by
    intro f hf hfne w hw
    have hbf : b f = f := (mem_F f).mp hf
    have hbaf : b (a f) = a (a f) := by
      have h := congrArg (fun g : MulAut X => g f) hba
      simpa [MulAut.mul_apply, pow_two, hbf] using h
    have hmap : Subgroup.map b.toMonoidHom (Subgroup.closure ({f, a f} : Set X)) =
        Subgroup.closure ({b f, b (a f)} : Set X) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z; simp
    have hle : Subgroup.closure ({b f, b (a f)} : Set X) ≤
        Subgroup.closure ({f, a f} : Set X) := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [hbf]; exact Subgroup.subset_closure (by simp)
      · rw [hbaf, ha2v f hfne]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    have hmem : b w ∈ Subgroup.map b.toMonoidHom (Subgroup.closure ({f, a f} : Set X)) :=
      ⟨w, hw, rfl⟩
    rw [hmap] at hmem
    exact hle hmem
  have mem_inter_F : ∀ f : X, f ∈ F → f ≠ 1 → ∀ z : X,
      z ∈ Subgroup.closure ({f, a f} : Set X) → z ∈ F → z = 1 ∨ z = f := by
    intro f hf hfne z hzW hzF
    have hbf : b f = f := (mem_F f).mp hf
    have hbaf : b (a f) = a (a f) := by
      have h := congrArg (fun g : MulAut X => g f) hba
      simpa [MulAut.mul_apply, pow_two, hbf] using h
    rcases (mem_W f hfne z).mp hzW with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have hbz : b (a f) = a f := (mem_F (a f)).mp hzF
      rw [hbaf, ha2v f hfne] at hbz
      exact hva_ne_av f hfne hbz
    · exfalso
      have hbz : b (f * a f) = f * a f := (mem_F (f * a f)).mp hzF
      rw [map_mul, hbf, hbaf, ha2v f hfne] at hbz
      have hL : f * (f * a f) = a f := by rw [← mul_assoc, ← pow_two, hsq f, one_mul]
      exact hva_ne_av f hfne (hbz.symm.trans hL)
  let S := {f : X // f ∈ F ∧ f ≠ 1}
  let Φ : S → {W : Subgroup X // Nat.card W = 4 ∧ (∀ w ∈ W, a w ∈ W) ∧
      (∀ w ∈ W, b w ∈ W)} := fun f =>
    ⟨Subgroup.closure ({f.1, a f.1} : Set X), hcardW f.1 f.2.2, a_inv_W f.1 f.2.2,
      b_inv_W f.1 f.2.1 f.2.2⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨f, hfF, hfne⟩ ⟨g, hgF, hgne⟩ heq
    apply Subtype.ext
    have hW : Subgroup.closure ({f, a f} : Set X) = Subgroup.closure ({g, a g} : Set X) :=
      congrArg Subtype.val heq
    have hgW : g ∈ Subgroup.closure ({f, a f} : Set X) := by
      rw [hW]
      exact Subgroup.subset_closure (by simp)
    rcases mem_inter_F f hfF hfne g hgW hgF with h | h
    · exact absurd h hgne
    · exact h.symm
  have hsurj : Function.Surjective Φ := by
    rintro ⟨W, hWcard, hWa, hWb⟩
    have hge2 : 2 ≤ Nat.card ↥(W ⊓ F) := by
      let g : ↥W →* X := φ.comp W.subtype
      have hker_eq : g.ker = F.subgroupOf W := rfl
      have hker_card : Nat.card g.ker = Nat.card ↥(W ⊓ F) := by
        rw [hker_eq, ← Subgroup.card_map_of_injective (K := F.subgroupOf W) W.subtype_injective,
          Subgroup.subgroupOf_map_subtype, inf_comm]
      have hrange_le : g.range ≤ W ⊓ F := by
        rintro x ⟨w, rfl⟩
        refine ⟨?_, ?_⟩
        · change (w : X) * b (w : X) ∈ W
          exact W.mul_mem w.2 (hWb w w.2)
        · change g w ∈ F
          rw [mem_F]
          change b (g w) = g w
          change b ((w : X) * b (w : X)) = (w : X) * b (w : X)
          rw [map_mul, hbb, comm (b (w : X)) (w : X)]
      have hle : Nat.card g.range ≤ Nat.card ↥(W ⊓ F) :=
        Nat.card_le_card_of_injective (Set.inclusion hrange_le) (Set.inclusion_injective hrange_le)
      have hck := Subgroup.card_ker_mul_card_range g
      have h4 : Nat.card g.ker * Nat.card g.range = 4 := by
        rw [hck]
        exact hWcard
      rw [hker_card] at h4
      have hsq : 4 ≤ Nat.card ↥(W ⊓ F) * Nat.card ↥(W ⊓ F) := by
        calc 4 = Nat.card ↥(W ⊓ F) * Nat.card g.range := h4.symm
          _ ≤ Nat.card ↥(W ⊓ F) * Nat.card ↥(W ⊓ F) := Nat.mul_le_mul (le_refl _) hle
      by_contra h
      push Not at h
      have hle1 : Nat.card ↥(W ⊓ F) ≤ 1 := by omega
      have h1 : Nat.card ↥(W ⊓ F) * Nat.card ↥(W ⊓ F) ≤ 1 := by
        calc Nat.card ↥(W ⊓ F) * Nat.card ↥(W ⊓ F) ≤ 1 * 1 := Nat.mul_le_mul hle1 hle1
          _ = 1 := by norm_num
      omega
    obtain ⟨f, hfne⟩ : ∃ f : ↥(W ⊓ F), f ≠ 1 := by
      haveI : Nontrivial ↥(W ⊓ F) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      exact exists_ne 1
    refine ⟨⟨(f : X), f.2.2, fun h => hfne (Subtype.ext h)⟩, ?_⟩
    apply Subtype.ext
    show Subgroup.closure ({(f : X), a (f : X)} : Set X) = W
    have hleW : Subgroup.closure ({(f : X), a (f : X)} : Set X) ≤ W := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact f.2.1
      · exact hWa (f : X) f.2.1
    exact Subgroup.eq_of_le_of_card_ge hleW
      (by rw [hWcard, hcardW (f : X) (fun h => hfne (Subtype.ext h))])
  have hS3 : Nat.card S = 3 := by
    change Nat.card {f : X // f ∈ F ∧ f ≠ 1} = 3
    have hcard : Nat.card {f : X // f ∈ F ∧ f ≠ 1} = ((F : Set X) \ {1}).ncard := by
      show ({f : X | f ∈ F ∧ f ≠ 1} : Set X).ncard = ((F : Set X) \ {1}).ncard
      rw [show ({f : X | f ∈ F ∧ f ≠ 1} : Set X) = (F : Set X) \ {1} from by
        ext z; simp [Set.mem_sdiff]]
    rw [hcard, Set.ncard_sdiff_singleton_of_mem F.one_mem]
    have hFs : (F : Set X).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hcardF
    omega
  calc Nat.card {W : Subgroup X // Nat.card W = 4 ∧ (∀ w ∈ W, a w ∈ W) ∧
        (∀ w ∈ W, b w ∈ W)}
      = Nat.card S := (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm
    _ = 3 := hS3

end Core

theorem lemma38 (hρ : IsAutE16 ρ) {H : Subgroup G}
    (hH : Nonempty (↥H ≃* Equiv.Perm (Fin 3)))
    (hV : actFixed ρ (CFSG.Open.pCoreOf 3 H : Set G) = ⊥) :
    Nat.card {W : Subgroup V // Nat.card W = 4 ∧ ∀ h ∈ H, ∀ w ∈ W, ρ h w ∈ W} = 3 := by
  classical
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hρ.card_eq]; norm_num)
  obtain ⟨e⟩ := hH
  let rH : ↥H := e.symm (finRotate 3)
  let lH : ↥H := e.symm (Equiv.swap 0 1)
  let r : G := rH
  let l : G := lH
  let a : MulAut V := ρ r
  let b : MulAut V := ρ l
  have her : e rH = finRotate 3 := e.apply_symm_apply _
  have hel : e lH = Equiv.swap 0 1 := e.apply_symm_apply _
  have hc3 : (finRotate 3 : Equiv.Perm (Fin 3)) ^ 3 = 1 := by decide
  have hs2 : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) ^ 2 = 1 := by decide
  have hscs : (Equiv.swap 0 1) * (finRotate 3) * (Equiv.swap 0 1)⁻¹ =
      (finRotate 3) ^ 2 := by decide
  have hrH3 : rH ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one, her]
    exact hc3
  have hlH2 : lH ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, hel]
    exact hs2
  have hlHrH : lH * rH * lH⁻¹ = rH ^ 2 := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, map_pow, her, hel]
    exact hscs
  have hr3 : r ^ 3 = 1 := by simpa [r] using congrArg H.subtype hrH3
  have hl2 : l ^ 2 = 1 := by simpa [l] using congrArg H.subtype hlH2
  have hrl : l * r * l⁻¹ = r ^ 2 := by simpa [r, l] using congrArg H.subtype hlHrH
  have ha3 : a ^ 3 = 1 := by
    have h := congrArg ρ hr3
    simpa [a, map_pow] using h
  have hb2 : b ^ 2 = 1 := by
    have h := congrArg ρ hl2
    simpa [b, map_pow] using h
  have hrel : b * a * b⁻¹ = a ^ 2 := by
    have h := congrArg ρ hrl
    simpa [a, b, map_pow] using h
  have hcube : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 →
      σ = 1 ∨ σ = finRotate 3 ∨ σ = (finRotate 3) ^ 2 := by decide
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  have hfpf : ∀ v : V, a v = v → v = 1 := by
    intro v hv
    have hvmem : v ∈ actFixed ρ (CFSG.Open.pCoreOf 3 H : Set G) := by
      intro g hg
      change g ∈ (pCore 3 ↥H).map H.subtype at hg
      rw [Subgroup.mem_map] at hg
      obtain ⟨h, hhp, hhge⟩ := hg
      subst hhge
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 3) (G := ↥H) ⟨h, hhp⟩
      have hnH : h ^ (3 ^ n) = 1 := by
        have := congrArg (Subtype.val) hn
        simpa using this
      have hσ3 : (e h) ^ (3 ^ n) = 1 := by
        rw [← map_pow, hnH, map_one]
      have hdvd1 : orderOf (e h) ∣ 3 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hσ3
      have hdvd2 : orderOf (e h) ∣ 6 := by
        have := orderOf_dvd_natCard (e h)
        rwa [hperm] at this
      have hndvd2 : ¬ 2 ∣ orderOf (e h) := by
        intro h2
        have h23 : ¬ 2 ∣ 3 ^ n := fun hd => by
          have := Nat.prime_two.dvd_of_dvd_pow hd
          norm_num at this
        exact h23 (h2.trans hdvd1)
      have hcop : Nat.Coprime (orderOf (e h)) 2 :=
        (Nat.prime_two.coprime_iff_not_dvd.mpr hndvd2).symm
      have hdvd3 : orderOf (e h) ∣ 3 := by
        have h6 : orderOf (e h) ∣ 2 * 3 := by
          rwa [show (6 : ℕ) = 2 * 3 by norm_num] at hdvd2
        exact hcop.dvd_of_dvd_mul_left h6
      have hσ3' : (e h) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd3
      have h1 : e.symm (e h) = h := e.symm_apply_apply h
      rcases hcube (e h) hσ3' with hσ | hσ | hσ
      · rw [hσ, map_one] at h1
        rw [h1.symm]
        simp
      · rw [hσ] at h1
        rw [h1.symm]
        change a v = v
        exact hv
      · rw [hσ, map_pow] at h1
        rw [h1.symm]
        have hsub : (H.subtype (rH ^ 2) : G) = r ^ 2 := by rw [map_pow]; rfl
        rw [hsub, map_pow]
        change (a ^ 2) v = v
        rw [pow_two, MulAut.mul_apply, hv, hv]
    rw [hV] at hvmem
    simpa using hvmem
  have hgen : Subgroup.closure ({finRotate 3, Equiv.swap 0 1} :
      Set (Equiv.Perm (Fin 3))) = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    have h6all : ∀ τ : Equiv.Perm (Fin 3), τ = 1 ∨ τ = finRotate 3 ∨
        τ = (finRotate 3) ^ 2 ∨ τ = Equiv.swap 0 1 ∨
        τ = finRotate 3 * Equiv.swap 0 1 ∨ τ = (finRotate 3) ^ 2 * Equiv.swap 0 1 :=
      by decide
    rcases h6all σ with h | h | h | h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2)
        (Subgroup.subset_closure (by simp))
  have hHgen : H = Subgroup.closure ({r, l} : Set G) := by
    have htopH : Subgroup.closure ({rH, lH} : Set ↥H) = ⊤ := by
      refine (Subgroup.map_injective (f := e.toMonoidHom) e.injective).eq_iff.mp ?_
      rw [MonoidHom.map_closure,
        show e.toMonoidHom '' ({rH, lH} : Set ↥H) = {finRotate 3, Equiv.swap 0 1} from by
          ext x; simp [rH, lH],
        hgen, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    calc H = (⊤ : Subgroup ↥H).map H.subtype := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = (Subgroup.closure ({rH, lH} : Set ↥H)).map H.subtype := by rw [htopH]
      _ = Subgroup.closure ({r, l} : Set G) := by
          rw [MonoidHom.map_closure]
          congr 1
          ext x; simp [r, l, rH, lH]
  have inv_iff : ∀ W : Subgroup V,
      (∀ h ∈ H, ∀ w ∈ W, ρ h w ∈ W) ↔
        (∀ w ∈ W, a w ∈ W) ∧ (∀ w ∈ W, b w ∈ W) := by
    intro W
    constructor
    · intro hfin
      exact ⟨fun w hw => hfin r (by rw [hHgen]; exact Subgroup.subset_closure (by simp)) w hw,
        fun w hw => hfin l (by rw [hHgen]; exact Subgroup.subset_closure (by simp)) w hw⟩
    · intro ⟨ha, hb⟩ h hh
      let S : Subgroup G :=
        { carrier := {g | ∀ w ∈ W, ρ g w ∈ W}
          one_mem' := by intro w hw; rw [map_one]; exact hw
          mul_mem' := by
            intro g g' hg hg' w hw
            rw [map_mul, MulAut.mul_apply]
            exact hg _ (hg' w hw)
          inv_mem' := by
            intro g hg w hw
            have hmap_le : W.map (ρ g).toMonoidHom ≤ W := by
              rintro x ⟨y, hy, rfl⟩
              exact hg y hy
            have hcardmap : Nat.card (W.map (ρ g).toMonoidHom) = Nat.card W :=
              Subgroup.card_map_of_injective (K := W) (ρ g).injective
            have heq : W.map (ρ g).toMonoidHom = W :=
              Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcardmap.symm)
            have hw' : w ∈ W.map (ρ g).toMonoidHom := by rwa [heq]
            rcases hw' with ⟨y, hy, hyw⟩
            have hconv : ρ g⁻¹ w = y := by
              rw [← hyw, map_inv]
              exact (ρ g).symm_apply_apply y
            rw [hconv]
            exact hy }
      have hle : H ≤ S := by
        rw [hHgen, Subgroup.closure_le]
        rintro g (rfl | rfl)
        · exact ha
        · exact hb
      exact hle hh
  have hcore := core hρ.card_eq hρ.sq_eq_one a b ha3 hb2 hrel hfpf
  rw [show Nat.card {W : Subgroup V // Nat.card W = 4 ∧ ∀ h ∈ H, ∀ w ∈ W, ρ h w ∈ W} =
      Nat.card {W : Subgroup V // Nat.card W = 4 ∧ (∀ w ∈ W, a w ∈ W) ∧
        (∀ w ∈ W, b w ∈ W)} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun W => and_congr Iff.rfl (inv_iff W)))]
  exact hcore

end CFSG.OddStandard.SmallF3.HarrisU33
