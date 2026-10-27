module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Setup
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoJ

public section

namespace CFSG.OddStandard.AltStdSmall4.N0

open Subgroup Equiv Equiv.Perm AltStdCycTwo
open scoped Pointwise

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

section Model

variable (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)

@[expose] def eps (i : Fin 8) : G := ((θ.symm ⟨tr hn i, tr_mem_alternatingGroup hn i⟩ : L) : G)

@[expose] def sg : G := ((θ.symm (sbA hn) : L) : G)

@[expose] def lam (f : Perm (Fin 8)) (hs : sign f = 1) : G :=
  ((θ.symm (extA hn f hs) : L) : G)

theorem eps_mem_L (i : Fin 8) : eps θ hn i ∈ L :=
  (θ.symm ⟨tr hn i, tr_mem_alternatingGroup hn i⟩).2

theorem sg_mem_L : sg θ hn ∈ L := (θ.symm (sbA hn)).2

theorem lam_mem_L (f : Perm (Fin 8)) (hs : sign f = 1) : lam θ hn f hs ∈ L :=
  (θ.symm (extA hn f hs)).2

theorem eps_mul (i j : Fin 8) : eps θ hn i * eps θ hn j = eps θ hn (i ^^^ j) := by
  have h : (⟨tr hn i, tr_mem_alternatingGroup hn i⟩ : alternatingGroup (Fin n)) *
      ⟨tr hn j, tr_mem_alternatingGroup hn j⟩ = ⟨tr hn (i ^^^ j), tr_mem_alternatingGroup hn _⟩ :=
    Subtype.ext ((tr_mul_tr hn i j).trans (congrArg (tr hn) (xr_eq_xor i j)))
  simp only [eps, ← Subgroup.coe_mul, ← map_mul, h]

theorem eps_zero : eps θ hn 0 = 1 := by
  have h : (⟨tr hn 0, tr_mem_alternatingGroup hn 0⟩ : alternatingGroup (Fin n)) = 1 :=
    Subtype.ext (tr_zero hn)
  simp [eps, h]

theorem eps_injective : Function.Injective (eps θ hn) := by
  intro i j h
  have h1 : (⟨tr hn i, tr_mem_alternatingGroup hn i⟩ : alternatingGroup (Fin n)) =
      ⟨tr hn j, tr_mem_alternatingGroup hn j⟩ := θ.symm.injective (Subtype.ext h)
  exact tr_injective hn (congrArg Subtype.val h1)

theorem eps_comm (i j : Fin 8) : eps θ hn i * eps θ hn j = eps θ hn j * eps θ hn i := by
  rw [eps_mul, eps_mul]
  congr 1
  revert i j
  decide

theorem eps_mul_self (i : Fin 8) : eps θ hn i * eps θ hn i = 1 := by
  rw [eps_mul]
  have : i ^^^ i = 0 := by revert i; decide
  rw [this, eps_zero]

theorem eps_inv (i : Fin 8) : (eps θ hn i)⁻¹ = eps θ hn i :=
  inv_eq_of_mul_eq_one_right (eps_mul_self θ hn i)

theorem eps_eq_one_iff (i : Fin 8) : eps θ hn i = 1 ↔ i = 0 := by
  rw [← eps_zero θ hn]
  exact (eps_injective θ hn).eq_iff

theorem mem_E_iff (x : G) : x ∈ E θ hn ↔ ∃ i, x = eps θ hn i := by
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨i, hi⟩ := (mem_eBar_iff hn).1 ha
    obtain rfl : a = ⟨tr hn i, tr_mem_alternatingGroup hn i⟩ := Subtype.ext hi
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact mem_E_of_mem_eBar θ hn ((mem_eBar_iff hn).2 ⟨i, rfl⟩)

theorem eps_mem_E (i : Fin 8) : eps θ hn i ∈ E θ hn := (mem_E_iff θ hn _).2 ⟨i, rfl⟩

theorem w_eq_eps : w θ hn = eps θ hn 1 := by
  have h : wBar hn = ⟨tr hn 1, tr_mem_alternatingGroup hn 1⟩ := Subtype.ext (coe_wBar hn)
  simp only [w, eps, h]

theorem mem_centralizer_E_iff (x : G) :
    x ∈ centralizer (E θ hn : Set G) ↔ ∀ i, x * eps θ hn i = eps θ hn i * x := by
  rw [mem_centralizer_iff]
  constructor
  · intro h i
    exact (h _ (eps_mem_E θ hn i)).symm
  · intro h y hy
    obtain ⟨i, rfl⟩ := (mem_E_iff θ hn y).1 hy
    exact (h i).symm

theorem sg_conj_eps (i : Fin 8) : sg θ hn * eps θ hn i * (sg θ hn)⁻¹ = eps θ hn (mPerm i) := by
  simp only [sg, eps, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
    sbA_conj_tr]

theorem lam_conj_eps {f : Perm (Fin 8)} (hf : IsXorAdd f) (hs : sign f = 1) (i : Fin 8) :
    lam θ hn f hs * eps θ hn i * (lam θ hn f hs)⁻¹ = eps θ hn (f i) := by
  simp only [lam, eps, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
    extA_conj_tr hn hf hs]

theorem pow_conj_eps {t : G} (ht : ∀ i, t * eps θ hn i * t⁻¹ = eps θ hn (mPerm i)) (k : ℕ)
    (i : Fin 8) : t ^ k * eps θ hn i * (t ^ k)⁻¹ = eps θ hn ((mPerm ^ k) i) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_inv_rev, show t ^ k * t * eps θ hn i * (t⁻¹ * (t ^ k)⁻¹) =
      t ^ k * (t * eps θ hn i * t⁻¹) * (t ^ k)⁻¹ by group, ht, ih, pow_succ, Perm.mul_apply]

end Model

section Config

variable [Finite G] {Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
  (hn : 8 ≤ n) (c : Config G L Q n θ z)

include c

theorem comm_z_of_mem_L {l : G} (hl : l ∈ L) : l * z = z * l :=
  (mem_centralizer_singleton_iff.1 (le_cent_single c.ot.std c.ot.cyc hl))

theorem eps_comm_z (i : Fin 8) : eps θ hn i * z = z * eps θ hn i :=
  comm_z_of_mem_L c (eps_mem_L θ hn i)

theorem conj_z_not_mem_L (g : G) : g * z * g⁻¹ ∉ L :=
  not_conj_mem_L c.ot.std θ c.hn8 c.ot.cyc c.ot.card g

theorem z_not_mem_L : z ∉ L := by
  have := conj_z_not_mem_L c 1
  simpa using this

theorem z_ne_eps (i : Fin 8) : z ≠ eps θ hn i := fun h =>
  z_not_mem_L c (h ▸ eps_mem_L θ hn i)

theorem mem_B0_iff (x : G) :
    x ∈ E θ hn ⊔ zpowers z ↔ ∃ i, x = eps θ hn i ∨ x = z * eps θ hn i := by
  have hle : zpowers z ≤ normalizer (E θ hn : Set G) := by
    rw [zpowers_le]
    apply mem_normalizer_fintype
    intro y hy
    obtain ⟨i, rfl⟩ := (mem_E_iff θ hn y).1 hy
    rw [← eps_comm_z hn c, mul_inv_cancel_right]
    exact eps_mem_E θ hn i
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (E θ hn) (zpowers z) hle
  constructor
  · intro hx
    have hx' : x ∈ ((E θ hn : Set G) * (zpowers z : Set G)) := by
      rw [← hset]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
    obtain ⟨i, rfl⟩ := (mem_E_iff θ hn a).1 ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    have hz2 : z ^ (2 : ℤ) = 1 := by
      rw [zpow_two, c.ot.cyc.mul_self]
    have hk : z ^ k = z ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, hz2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · refine ⟨i, Or.inl ?_⟩
      rw [hk, h, zpow_zero, mul_one]
    · refine ⟨i, Or.inr ?_⟩
      rw [hk, h, zpow_one, eps_comm_z hn c]
  · rintro ⟨i, rfl | rfl⟩
    · exact mem_sup_left (eps_mem_E θ hn i)
    · exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left (eps_mem_E θ hn i))

theorem z_mem_B0 : z ∈ E θ hn ⊔ zpowers z := mem_sup_right (mem_zpowers z)

theorem eps_mem_B0 (i : Fin 8) : eps θ hn i ∈ E θ hn ⊔ zpowers z :=
  mem_sup_left (eps_mem_E θ hn i)

theorem mem_N0_of_mem_L {l : G} (hl : l ∈ L) (h : ∀ i, ∃ j, l * eps θ hn i * l⁻¹ = eps θ hn j) :
    l ∈ N0 θ hn z := by
  apply mem_normalizer_fintype
  intro x hx
  obtain ⟨i, rfl | rfl⟩ := (mem_B0_iff hn c x).1 hx
  · obtain ⟨j, hj⟩ := h i
    rw [hj]
    exact eps_mem_B0 hn c j
  · obtain ⟨j, hj⟩ := h i
    have : l * (z * eps θ hn i) * l⁻¹ = z * eps θ hn j := by
      rw [← hj, show l * (z * eps θ hn i) * l⁻¹ = (l * z) * eps θ hn i * l⁻¹ by group,
        comm_z_of_mem_L c hl]
      group
    rw [this]
    exact (mem_B0_iff hn c _).2 ⟨j, Or.inr rfl⟩

theorem sg_mem_N0 : sg θ hn ∈ N0 θ hn z :=
  mem_N0_of_mem_L hn c (sg_mem_L θ hn) fun i => ⟨mPerm i, sg_conj_eps θ hn i⟩

theorem lam_mem_N0 {f : Perm (Fin 8)} (hf : IsXorAdd f) (hs : sign f = 1) :
    lam θ hn f hs ∈ N0 θ hn z :=
  mem_N0_of_mem_L hn c (lam_mem_L θ hn f hs) fun i => ⟨f i, lam_conj_eps θ hn hf hs i⟩

theorem sg_comm_z : sg θ hn * z = z * sg θ hn := comm_z_of_mem_L c (sg_mem_L θ hn)

theorem conj_z_eq {g : G} (hg : g ∈ N0 θ hn z) : ∃ i, g * z * g⁻¹ = z * eps θ hn i := by
  have h1 : g * z * g⁻¹ ∈ E θ hn ⊔ zpowers z := (mem_normalizer_iff.1 hg z).1 (z_mem_B0 hn c)
  obtain ⟨i, h | h⟩ := (mem_B0_iff hn c _).1 h1
  · exact absurd (h ▸ eps_mem_L θ hn i) (conj_z_not_mem_L c g)
  · exact ⟨i, h⟩

variable (hF : ∃ g ∈ N0 θ hn z, g * z * g⁻¹ = z * w θ hn)

include hF

theorem exists_conj_z_eq (i : Fin 8) : ∃ g ∈ N0 θ hn z, g * z * g⁻¹ = z * eps θ hn i := by
  obtain ⟨g₀, hg₀, hg₀z⟩ := hF
  rw [w_eq_eps] at hg₀z
  by_cases hi : i = 0
  · exact ⟨1, one_mem _, by rw [hi, eps_zero]; group⟩
  obtain ⟨k, hk⟩ := exists_mPerm_pow_eq 1 i (by decide) hi
  refine ⟨sg θ hn ^ k * g₀, mul_mem (pow_mem (sg_mem_N0 hn c) k) hg₀, ?_⟩
  have hcomm : sg θ hn ^ k * z = z * sg θ hn ^ k :=
    (Commute.pow_left (sg_comm_z hn c) k).eq
  calc sg θ hn ^ k * g₀ * z * (sg θ hn ^ k * g₀)⁻¹
      = sg θ hn ^ k * (g₀ * z * g₀⁻¹) * (sg θ hn ^ k)⁻¹ := by group
    _ = sg θ hn ^ k * z * eps θ hn 1 * (sg θ hn ^ k)⁻¹ := by rw [hg₀z]; group
    _ = z * (sg θ hn ^ k * eps θ hn 1 * (sg θ hn ^ k)⁻¹) := by rw [hcomm]; group
    _ = z * eps θ hn i := by rw [pow_conj_eps θ hn (sg_conj_eps θ hn), hk]

theorem conj_eps_eq {g : G} (hg : g ∈ N0 θ hn z) (i : Fin 8) :
    ∃ j, g * eps θ hn i * g⁻¹ = eps θ hn j := by
  have h1 : g * eps θ hn i * g⁻¹ ∈ E θ hn ⊔ zpowers z :=
    (mem_normalizer_iff.1 hg _).1 (eps_mem_B0 hn c i)
  obtain ⟨j, h | h⟩ := (mem_B0_iff hn c _).1 h1
  · exact ⟨j, h⟩
  · exfalso
    obtain ⟨h', hh', hh'z⟩ := exists_conj_z_eq hn c hF j
    apply conj_z_not_mem_L c (g⁻¹ * h')
    have : g⁻¹ * h' * z * (g⁻¹ * h')⁻¹ = eps θ hn i := by
      calc g⁻¹ * h' * z * (g⁻¹ * h')⁻¹ = g⁻¹ * (h' * z * h'⁻¹) * g := by group
        _ = g⁻¹ * (g * eps θ hn i * g⁻¹) * g := by rw [hh'z, h]
        _ = eps θ hn i := by group
    rw [this]
    exact eps_mem_L θ hn i

theorem N0_le_normalizer_E : N0 θ hn z ≤ normalizer (E θ hn : Set G) := by
  intro g hg
  apply mem_normalizer_fintype
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_E_iff θ hn x).1 hx
  obtain ⟨j, hj⟩ := conj_eps_eq hn c hF hg i
  rw [hj]
  exact eps_mem_E θ hn j

theorem exists_act (g : G) (hg : g ∈ N0 θ hn z) :
    ∃ f : Perm (Fin 8), IsXorAdd f ∧ ∀ i, g * eps θ hn i * g⁻¹ = eps θ hn (f i) := by
  choose f₀ hf₀ using conj_eps_eq hn c hF hg
  have hinj : Function.Injective f₀ := by
    intro i j hij
    apply eps_injective θ hn
    have h1 := hf₀ i
    have h2 := hf₀ j
    rw [hij, ← h2] at h1
    simpa using h1
  have hbij : Function.Bijective f₀ := Finite.injective_iff_bijective.1 hinj
  refine ⟨Equiv.ofBijective f₀ hbij, fun i j => ?_, fun i => hf₀ i⟩
  apply eps_injective θ hn
  simp only [Equiv.ofBijective_apply]
  rw [← eps_mul, ← hf₀, ← hf₀, ← hf₀, ← eps_mul]
  group

end Config

@[expose] def D0 (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) : Subgroup G :=
  N0 θ hn z ⊓ centralizer (E θ hn : Set G)

section D0

variable [Finite G] {Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
  (hn : 8 ≤ n) (c : Config G L Q n θ z)
  (hF : ∃ g ∈ N0 θ hn z, g * z * g⁻¹ = z * w θ hn)

include c hF

theorem conj_mem_D0 {g : G} (hg : g ∈ N0 θ hn z) {d : G} (hd : d ∈ D0 θ hn z) :
    g * d * g⁻¹ ∈ D0 θ hn z := by
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hg (Subgroup.mem_inf.1 hd).1) (inv_mem hg), ?_⟩
  rw [mem_centralizer_E_iff]
  intro i
  obtain ⟨j, hj⟩ := conj_eps_eq hn c hF (inv_mem hg) i
  rw [inv_inv] at hj
  have hdj := (mem_centralizer_E_iff θ hn d).1 (Subgroup.mem_inf.1 hd).2 j
  calc g * d * g⁻¹ * eps θ hn i = g * (d * (g⁻¹ * eps θ hn i * g)) * g⁻¹ := by group
    _ = g * (d * eps θ hn j) * g⁻¹ := by rw [hj]
    _ = g * (eps θ hn j * d) * g⁻¹ := by rw [hdj]
    _ = g * (g⁻¹ * eps θ hn i * g) * d * g⁻¹ := by rw [hj]; group
    _ = eps θ hn i * (g * d * g⁻¹) := by group

private theorem conj_z_eq_of_sign (hD : ∀ d ∈ D0 θ hn z, d * z * d⁻¹ = z) {g g' : G}
    (hg : g ∈ N0 θ hn z) (hg' : g' ∈ N0 θ hn z) {f f' : Perm (Fin 8)} (hf : IsXorAdd f)
    (hf' : IsXorAdd f') (hfg : ∀ i, g * eps θ hn i * g⁻¹ = eps θ hn (f i))
    (hfg' : ∀ i, g' * eps θ hn i * g'⁻¹ = eps θ hn (f' i)) (hs : sign f = sign f') :
    g * z * g⁻¹ = g' * z * g'⁻¹ := by
  have hφ : IsXorAdd (f⁻¹ * f') := hf.inv.mul hf'
  have hsφ : sign (f⁻¹ * f') = 1 := by
    rw [Perm.sign_mul, Perm.sign_inv, hs, ← sq, Int.units_sq]
  set l := lam θ hn (f⁻¹ * f') hsφ with hl
  have hlN : l ∈ N0 θ hn z := lam_mem_N0 hn c hφ hsφ
  have hlE : ∀ i, l * eps θ hn i * l⁻¹ = eps θ hn ((f⁻¹ * f') i) := lam_conj_eps θ hn hφ hsφ
  have hginv : ∀ j, g⁻¹ * eps θ hn j * g = eps θ hn (f⁻¹ j) := by
    intro j
    have := hfg (f⁻¹ j)
    rw [show f (f⁻¹ j) = j by simp] at this
    rw [← this]
    group
  set d := l⁻¹ * g⁻¹ * g' with hd
  have hdN : d ∈ N0 θ hn z := mul_mem (mul_mem (inv_mem hlN) (inv_mem hg)) hg'
  have hdC : d ∈ centralizer (E θ hn : Set G) := by
    rw [mem_centralizer_E_iff]
    intro i
    have h1 : d * eps θ hn i * d⁻¹ = eps θ hn i := by
      calc d * eps θ hn i * d⁻¹ = l⁻¹ * (g⁻¹ * (g' * eps θ hn i * g'⁻¹) * g) * l := by
            rw [hd]; group
        _ = l⁻¹ * eps θ hn ((f⁻¹ * f') i) * l := by
            rw [hfg', hginv, Perm.mul_apply]
        _ = eps θ hn i := by rw [← hlE]; group
    calc d * eps θ hn i = d * eps θ hn i * d⁻¹ * d := by group
      _ = eps θ hn i * d := by rw [h1]
  have hdz := hD d ⟨hdN, hdC⟩
  have hlz : l * z = z * l := comm_z_of_mem_L c (lam_mem_L θ hn _ hsφ)
  have hg'eq : g' = g * l * d := by rw [hd]; group
  rw [hg'eq]
  calc g * z * g⁻¹ = g * (l * z * l⁻¹) * g⁻¹ := by rw [hlz]; group
    _ = g * l * (d * z * d⁻¹) * l⁻¹ * g⁻¹ := by rw [hdz]; group
    _ = g * l * d * z * (g * l * d)⁻¹ := by group

theorem exists_D0_ne : ∃ d ∈ D0 θ hn z, d * z * d⁻¹ ≠ z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g₀, hg₀, hg₀z⟩ := id hF
  rw [w_eq_eps] at hg₀z
  set g₃ := sg θ hn * g₀ * (sg θ hn)⁻¹ with hg₃
  have hg₃N : g₃ ∈ N0 θ hn z :=
    mul_mem (mul_mem (sg_mem_N0 hn c) hg₀) (inv_mem (sg_mem_N0 hn c))
  have hg₃z : g₃ * z * g₃⁻¹ = z * eps θ hn 2 := by
    have h2 : (2 : Fin 8) = mPerm 1 := by decide
    calc g₃ * z * g₃⁻¹ = sg θ hn * (g₀ * ((sg θ hn)⁻¹ * z * sg θ hn) * g₀⁻¹) * (sg θ hn)⁻¹ := by
          rw [hg₃]; group
      _ = sg θ hn * (g₀ * z * g₀⁻¹) * (sg θ hn)⁻¹ := by
          rw [show (sg θ hn)⁻¹ * z * sg θ hn = z by
            rw [mul_assoc, ← sg_comm_z hn c]; group]
      _ = z * (sg θ hn * eps θ hn 1 * (sg θ hn)⁻¹) := by
          rw [hg₀z, show sg θ hn * (z * eps θ hn 1) * (sg θ hn)⁻¹ =
            (sg θ hn * z) * eps θ hn 1 * (sg θ hn)⁻¹ by group, sg_comm_z hn c]
          group
      _ = z * eps θ hn 2 := by rw [sg_conj_eps, ← h2]
  obtain ⟨f₁, hf₁, hf₁g⟩ := exists_act hn c hF 1 (one_mem _)
  obtain ⟨f₂, hf₂, hf₂g⟩ := exists_act hn c hF g₀ hg₀
  obtain ⟨f₃, hf₃, hf₃g⟩ := exists_act hn c hF g₃ hg₃N
  have key := fun {g g' : G} (hg : g ∈ N0 θ hn z) (hg' : g' ∈ N0 θ hn z) {f f' : Perm (Fin 8)}
      (hf : IsXorAdd f) (hf' : IsXorAdd f') hfg hfg' (hs : sign f = sign f') =>
    conj_z_eq_of_sign hn c hF hcon hg hg' hf hf' hfg hfg' hs
  have hz1 : (1 : G) * z * 1⁻¹ = z := by group
  have hne12 : z ≠ z * eps θ hn 1 := by
    intro h
    have : eps θ hn 1 = 1 := by
      have := congrArg (z⁻¹ * ·) h
      simpa using this.symm
    exact absurd ((eps_eq_one_iff θ hn 1).1 this) (by decide)
  have hne13 : z ≠ z * eps θ hn 2 := by
    intro h
    have : eps θ hn 2 = 1 := by
      have := congrArg (z⁻¹ * ·) h
      simpa using this.symm
    exact absurd ((eps_eq_one_iff θ hn 2).1 this) (by decide)
  have hne23 : z * eps θ hn 1 ≠ z * eps θ hn 2 := by
    intro h
    have := eps_injective θ hn (mul_left_cancel h)
    exact absurd this (by decide)
  by_cases h12 : sign f₁ = sign f₂
  · have := key (one_mem _) hg₀ hf₁ hf₂ hf₁g hf₂g h12
    rw [hz1, hg₀z] at this
    exact hne12 this
  by_cases h13 : sign f₁ = sign f₃
  · have := key (one_mem _) hg₃N hf₁ hf₃ hf₁g hf₃g h13
    rw [hz1, hg₃z] at this
    exact hne13 this
  have h23 : sign f₂ = sign f₃ := by
    have e12 := Int.units_ne_iff_eq_neg.1 h12
    have e13 := Int.units_ne_iff_eq_neg.1 h13
    rw [e12] at e13
    exact neg_injective e13
  have := key hg₀ hg₃N hf₂ hf₃ hf₂g hf₃g h23
  rw [hg₀z, hg₃z] at this
  exact hne23 this

theorem exists_D0_conj_z_eq (j : Fin 8) : ∃ d ∈ D0 θ hn z, d * z * d⁻¹ = z * eps θ hn j := by
  have hstep : ∀ i, (∃ d ∈ D0 θ hn z, d * z * d⁻¹ = z * eps θ hn i) →
      ∃ d ∈ D0 θ hn z, d * z * d⁻¹ = z * eps θ hn (mPerm i) := by
    rintro i ⟨d, hd, hdz⟩
    refine ⟨sg θ hn * d * (sg θ hn)⁻¹, conj_mem_D0 hn c hF (sg_mem_N0 hn c) hd, ?_⟩
    calc sg θ hn * d * (sg θ hn)⁻¹ * z * (sg θ hn * d * (sg θ hn)⁻¹)⁻¹
        = sg θ hn * (d * ((sg θ hn)⁻¹ * z * sg θ hn) * d⁻¹) * (sg θ hn)⁻¹ := by group
      _ = sg θ hn * (d * z * d⁻¹) * (sg θ hn)⁻¹ := by
          rw [show (sg θ hn)⁻¹ * z * sg θ hn = z by rw [mul_assoc, ← sg_comm_z hn c]; group]
      _ = (sg θ hn * z) * eps θ hn i * (sg θ hn)⁻¹ := by rw [hdz]; group
      _ = z * (sg θ hn * eps θ hn i * (sg θ hn)⁻¹) := by rw [sg_comm_z hn c]; group
      _ = z * eps θ hn (mPerm i) := by rw [sg_conj_eps]
  have hpow : ∀ (k : ℕ) i, (∃ d ∈ D0 θ hn z, d * z * d⁻¹ = z * eps θ hn i) →
      ∃ d ∈ D0 θ hn z, d * z * d⁻¹ = z * eps θ hn ((mPerm ^ k) i) := by
    intro k
    induction k with
    | zero => intro i h; simpa using h
    | succ k ih =>
      intro i h
      rw [pow_succ', Perm.mul_apply]
      exact hstep _ (ih i h)
  by_cases hj : j = 0
  · exact ⟨1, one_mem _, by rw [hj, eps_zero]; group⟩
  obtain ⟨d₀, hd₀, hd₀z⟩ := exists_D0_ne hn c hF
  obtain ⟨j₀, hj₀⟩ := conj_z_eq hn c hd₀.1
  have hj₀0 : j₀ ≠ 0 := by
    intro h
    rw [h, eps_zero, mul_one] at hj₀
    exact hd₀z hj₀
  obtain ⟨k, hk⟩ := exists_mPerm_pow_eq j₀ j hj₀0 hj
  rw [← hk]
  exact hpow k j₀ ⟨d₀, hd₀, hj₀⟩

end D0

end CFSG.OddStandard.AltStdSmall4.N0
