module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAbSigma3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G]

private theorem conjAut_congr_aux {G : Type} [Group G] (H : Subgroup G) {g g' : G}
    (hg : g ∈ normalizer (H : Set G)) (hg' : g' ∈ normalizer (H : Set G)) (h : g = g') :
    Outside.conjAut H g hg = Outside.conjAut H g' hg' := by
  subst h
  exact congrArg (fun p => Outside.conjAut H g p) (Subsingleton.elim hg hg')

private theorem card_eq_sq_fix_comm {T : Type} [Group T] [Finite T]
    (hcomm : ∀ a b : T, a * b = b * a) {ρ x : MulAut T}
    (hρ : ρ ^ 3 = 1) (hfpf : ∀ g : T, ρ g = g → g = 1)
    (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) :
    Nat.card T = Nat.card ↥(Outside.fixSub x) ^ 2 := by
  classical
  letI : IsMulCommutative T := IsMulCommutative.of_comm hcomm
  have hxρ_apply : ∀ g : T, x (ρ g) = ρ⁻¹ (x g) := by
    intro g
    have h : x * ρ = ρ⁻¹ * x := by
      calc x * ρ = x * ρ * x⁻¹ * x := by group
        _ = ρ⁻¹ * x := by rw [hxρ]
    simpa [MulAut.mul_apply] using congrArg (fun f : MulAut T => f g) h
  have hxρinv_apply : ∀ g : T, x (ρ⁻¹ g) = ρ (x g) := by
    intro g
    have h := hxρ_apply (ρ⁻¹ g)
    rw [MulAut.apply_inv_self] at h
    have h' := congrArg ρ h
    rw [MulAut.apply_inv_self] at h'
    exact h'.symm
  have hxx_apply : ∀ g : T, x (x g) = g := by
    intro g
    simpa [MulAut.mul_apply] using congrArg (fun f : MulAut T => f g) hx
  have hρcube : ∀ g : T, ρ (ρ (ρ g)) = g := by
    intro g
    have h := congrArg (fun f : MulAut T => f g) hρ
    simpa [pow_succ, MulAut.mul_apply] using h
  let d : T →* T :=
    { toFun := fun u => ρ u * (ρ⁻¹ u)⁻¹
      map_one' := by simp
      map_mul' := by
        intro u v
        show ρ (u * v) * (ρ⁻¹ (u * v))⁻¹ = (ρ u * (ρ⁻¹ u)⁻¹) * (ρ v * (ρ⁻¹ v)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        ac_rfl }
  have hd_inj : Function.Injective d := by
    intro u v huv
    have h1 : d (u * v⁻¹) = 1 := by
      rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 : ρ (u * v⁻¹) = ρ⁻¹ (u * v⁻¹) := by
      apply mul_inv_eq_one.mp
      exact h1
    have h3 : ρ (u * v⁻¹) = u * v⁻¹ := by
      have hρ2 : ρ (ρ (u * v⁻¹)) = u * v⁻¹ := by
        calc ρ (ρ (u * v⁻¹)) = ρ (ρ⁻¹ (u * v⁻¹)) := by rw [h2]
          _ = u * v⁻¹ := by rw [MulAut.apply_inv_self]
      have h4 : ρ (ρ (ρ (u * v⁻¹))) = ρ (u * v⁻¹) := by rw [hρ2]
      rw [hρcube] at h4
      exact h4.symm
    exact mul_inv_eq_one.mp (hfpf (u * v⁻¹) h3)
  have hd_surj : Function.Surjective d :=
    (Finite.injective_iff_surjective).mp hd_inj
  let f : (↥(Outside.fixSub x) × ↥(Outside.fixSub x)) → T := fun p => p.1.1 * ρ p.2.1
  have hinj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hpq
    have hval : a * ρ b = a' * ρ b' := hpq
    have hax : x a = a := ha
    have hbx : x b = b := hb
    have ha'x : x a' = a' := ha'
    have hb'x : x b' = b' := hb'
    have hkey : a'⁻¹ * a = ρ (b' * b⁻¹) := by
      calc a'⁻¹ * a = a'⁻¹ * (a * ρ b) * (ρ b)⁻¹ := by group
        _ = a'⁻¹ * (a' * ρ b') * (ρ b)⁻¹ := by rw [hval]
        _ = ρ b' * (ρ b)⁻¹ := by group
        _ = ρ (b' * b⁻¹) := by rw [map_mul, map_inv]
    have hafix : x (a'⁻¹ * a) = a'⁻¹ * a := by rw [map_mul, map_inv, ha'x, hax]
    have hbfix : x (b' * b⁻¹) = b' * b⁻¹ := by rw [map_mul, map_inv, hb'x, hbx]
    have hone : a'⁻¹ * a = 1 :=
      Outside.eq_one_of_fix_eq_rho hρ hfpf hx hxρ hafix hbfix hkey
    have haeq : a = a' := (inv_mul_eq_one.mp hone).symm
    have hb_eq : b = b' := by
      have hρone : ρ (b' * b⁻¹) = 1 := by rw [← hkey, hone]
      have hb'eq : b' = b := mul_inv_eq_one.mp (ρ.injective (by rw [hρone, map_one]))
      exact hb'eq.symm
    exact Prod.ext (Subtype.ext haeq) (Subtype.ext hb_eq)
  have hsurj : Function.Surjective f := by
    intro n
    obtain ⟨b, hb⟩ := hd_surj (n * (x n)⁻¹)
    have hbval : ρ b * (ρ⁻¹ b)⁻¹ = n * (x n)⁻¹ := hb
    have hb' : x n * n⁻¹ = ρ⁻¹ b * (ρ b)⁻¹ := by
      have h := congrArg Inv.inv hbval
      rw [mul_inv_rev, inv_inv, mul_inv_rev, inv_inv] at h
      exact h.symm
    have hxm : x (n * (x n)⁻¹) = (n * (x n)⁻¹)⁻¹ := by
      rw [map_mul, map_inv, hxx_apply, mul_inv_rev, inv_inv]
    have hxd : x (d b) = (d b)⁻¹ := by rw [hb]; exact hxm
    have hxd' : x (d b) = (d (x b))⁻¹ := by
      change x (ρ b * (ρ⁻¹ b)⁻¹) = (ρ (x b) * (ρ⁻¹ (x b))⁻¹)⁻¹
      rw [map_mul, map_inv, hxρ_apply, hxρinv_apply, mul_inv_rev, inv_inv]
    have hdb : d (x b) = d b := by
      apply inv_injective
      rw [← hxd', hxd]
    have hxb : x b = b := hd_inj hdb
    refine ⟨(⟨n * (ρ b)⁻¹, ?_⟩, ⟨b, by simpa [Outside.fixSub] using hxb⟩), ?_⟩
    · show x (n * (ρ b)⁻¹) = n * (ρ b)⁻¹
      rw [map_mul, map_inv, hxρ_apply, hxb]
      have hxn : x n = n * ρ⁻¹ b * (ρ b)⁻¹ := by
        calc x n = x n * n⁻¹ * n := by group
          _ = (ρ⁻¹ b * (ρ b)⁻¹) * n := by rw [hb']
          _ = n * ρ⁻¹ b * (ρ b)⁻¹ := by ac_rfl
      rw [hxn]
      calc (n * ρ⁻¹ b * (ρ b)⁻¹) * (ρ⁻¹ b)⁻¹
          = n * ((ρ⁻¹ b) * (ρ⁻¹ b)⁻¹) * (ρ b)⁻¹ := by ac_rfl
        _ = n * (ρ b)⁻¹ := by rw [mul_inv_cancel]; group
    · show n * (ρ b)⁻¹ * ρ b = n
      group
  have hcard : Nat.card T = Nat.card (↥(Outside.fixSub x) × ↥(Outside.fixSub x)) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
  rw [hcard, Nat.card_prod, sq]

theorem card_eq_sq_card_inf_centralizer [Finite G] {A : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {rho sigma : G}
    (hrA : ∀ a ∈ A, rho * a * rho⁻¹ ∈ A) (hsA : ∀ a ∈ A, sigma * a * sigma⁻¹ ∈ A)
    (hrho : rho ^ 3 = 1) (hfpf : ∀ a ∈ A, rho * a * rho⁻¹ = a → a = 1)
    (hsig : sigma * sigma = 1) (hsr : sigma * rho * sigma⁻¹ = rho⁻¹) :
    Nat.card A = Nat.card ↥(A ⊓ centralizer ({sigma} : Set G)) ^ 2 := by
  classical
  have hρmem : rho ∈ normalizer (A : Set G) := Subgroup.mem_normalizer_fintype hrA
  have hσmem : sigma ∈ normalizer (A : Set G) := Subgroup.mem_normalizer_fintype hsA
  let ρ : MulAut A := Outside.conjAut A rho hρmem
  let σ : MulAut A := Outside.conjAut A sigma hσmem
  have hρ3 : ρ ^ 3 = 1 := by
    change (Outside.conjAut A rho hρmem) ^ 3 = 1
    have hp : (Outside.conjAut A rho hρmem) ^ 3
        = Outside.conjAut A (rho ^ 3) (pow_mem hρmem 3) :=
      (Outside.conjAut_pow A hρmem 3 (pow_mem hρmem 3)).symm
    have hp2 : Outside.conjAut A (rho ^ 3) (pow_mem hρmem 3) = 1 := by
      rw [conjAut_congr_aux A (pow_mem hρmem 3) (one_mem _) hrho]
      exact Outside.conjAut_one A _
    rw [hp, hp2]
  have hσ2 : σ * σ = 1 := by
    change Outside.conjAut A sigma hσmem * Outside.conjAut A sigma hσmem = 1
    have hp : Outside.conjAut A sigma hσmem * Outside.conjAut A sigma hσmem
        = Outside.conjAut A (sigma * sigma) (mul_mem hσmem hσmem) :=
      (Outside.conjAut_mul A hσmem hσmem (mul_mem hσmem hσmem)).symm
    have hp2 : Outside.conjAut A (sigma * sigma) (mul_mem hσmem hσmem) = 1 := by
      rw [conjAut_congr_aux A (mul_mem hσmem hσmem) (one_mem _) hsig]
      exact Outside.conjAut_one A _
    rw [hp, hp2]
  have hσρ : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    change Outside.conjAut A sigma hσmem * Outside.conjAut A rho hρmem
        * (Outside.conjAut A sigma hσmem)⁻¹ = (Outside.conjAut A rho hρmem)⁻¹
    have hexp : Outside.conjAut A sigma hσmem * Outside.conjAut A rho hρmem
        * (Outside.conjAut A sigma hσmem)⁻¹
        = Outside.conjAut A (sigma * rho * sigma⁻¹)
            (mul_mem (mul_mem hσmem hρmem) (inv_mem hσmem)) := by
      rw [Outside.conjAut_mul A (mul_mem hσmem hρmem) (inv_mem hσmem)
            (mul_mem (mul_mem hσmem hρmem) (inv_mem hσmem)),
          Outside.conjAut_mul A hσmem hρmem (mul_mem hσmem hρmem),
          Outside.conjAut_inv A hσmem (inv_mem hσmem)]
    rw [hexp]
    have hρi : rho⁻¹ ∈ normalizer (A : Set G) := inv_mem hρmem
    have key : Outside.conjAut A (sigma * rho * sigma⁻¹)
          (mul_mem (mul_mem hσmem hρmem) (inv_mem hσmem))
        = Outside.conjAut A (rho⁻¹) hρi :=
      conjAut_congr_aux A _ hρi hsr
    rw [key, Outside.conjAut_inv A hρmem hρi]
  have hfpf' : ∀ a : A, ρ a = a → a = 1 := by
    intro a ha
    apply Subtype.ext
    have hval : ((ρ a : A) : G) = (a : G) := congrArg Subtype.val ha
    change ((Outside.conjAut A rho hρmem a : A) : G) = (a : G) at hval
    rw [Outside.conjAut_coe] at hval
    exact hfpf a a.2 hval
  have hmain : Nat.card A = Nat.card ↥(Outside.fixSub σ) ^ 2 :=
    card_eq_sq_fix_comm (T := A) (fun a b => Subtype.ext (hcomm a a.2 b b.2)) hρ3 hfpf' hσ2 hσρ
  rw [hmain]
  congr 1
  have hmap := Outside.map_fixSub_conjAut A hσmem
  change Nat.card ↥(Outside.fixSub (Outside.conjAut A sigma hσmem))
      = Nat.card ↥(A ⊓ centralizer ({sigma} : Set G))
  rw [← hmap, Subgroup.card_map_of_injective A.subtype_injective]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
