module

public import CFSG.Quasithin.Background.InvolutionQuadratic
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltEnd
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltDih

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv
open CFSG.EvenSmallLie.OddTranspAlt (cls)
open scoped commutatorElement

section Basic

variable {V : Type} [CommGroup V]

private theorem commV_zpowers_conj (x g : MulAut V) :
    commV (Subgroup.zpowers (g * x * g⁻¹)) = (commV (Subgroup.zpowers x)).map g.toMonoidHom :=
  CFSG.Quasithin.commV_zpowers_conj_eq x g

private theorem mem_zpowers_sq {x : MulAut V} (hx : x ^ 2 = 1) {z : MulAut V}
    (hz : z ∈ Subgroup.zpowers x) : z = 1 ∨ z = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have h2 : (orderOf x : ℤ) ∣ 2 := by exact_mod_cast hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · left
    have : x = 1 := orderOf_eq_one_iff.mp h1
    rw [this, one_zpow]
  · have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rw [← zpow_mod_orderOf, h1]
    rcases hk with hk | hk
    · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
    · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]

theorem commV_zpowers_le_fixV_self (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hx : x ^ 2 = 1) : commV (Subgroup.zpowers x) ≤ fixV (Subgroup.zpowers x) :=
  CFSG.Quasithin.commV_zpowers_le_fixV_of_involution hV hx

private theorem commute_of_commV_eq (hV : ∀ v : V, v ^ 2 = 1) {x y : MulAut V} (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (h : commV (Subgroup.zpowers x) = commV (Subgroup.zpowers y)) :
    x * y = y * x := by
  have hfx := commV_zpowers_le_fixV_self hV hx
  have hfy := commV_zpowers_le_fixV_self hV hy
  ext v
  have hw : x v * v⁻¹ ∈ commV (Subgroup.zpowers x) :=
    Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, v, rfl⟩
  have hw' : y v * v⁻¹ ∈ commV (Subgroup.zpowers y) :=
    Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, v, rfl⟩
  have e1 : x (y v * v⁻¹) = y v * v⁻¹ :=
    mem_fixV.mp (hfx (h ▸ hw')) x (Subgroup.mem_zpowers x)
  have e2 : y (x v * v⁻¹) = x v * v⁻¹ :=
    mem_fixV.mp (hfy (h ▸ hw)) y (Subgroup.mem_zpowers y)
  have a1 : x (y v) = y v * v⁻¹ * x v := by
    have : x (y v * v⁻¹ * v) = x (y v * v⁻¹) * x v := map_mul x _ _
    rw [e1] at this
    simpa using this
  have a2 : y (x v) = x v * v⁻¹ * y v := by
    have : y (x v * v⁻¹ * v) = y (x v * v⁻¹) * y v := map_mul y _ _
    rw [e2] at this
    simpa using this
  show x (y v) = y (x v)
  rw [a1, a2]
  ac_rfl

end Basic

section Module

variable {V : Type} [CommGroup V] {m : ℕ}

theorem commV_zpowers_le_fixV (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m)
    {Y : Subgroup (MulAut V)} (θ : Y ≃* alternatingGroup (Fin m))
    (hnat : IsNatSectionWith (altAct m) θ (commV Y) ⊥) {t : MulAut V} (ht : t ^ 2 = 1)
    (hc : ∀ y ∈ Y, t * y = y * t) : commV (Subgroup.zpowers t) ≤ fixV Y := by
  have hsplit := commV_sup_fixV_of_natural hodd (by omega) θ hnat
  have htE := fix_commV_of_commute_natural hV hodd (by omega) θ hnat ht hc
  have htC : ∀ x ∈ fixV Y, t x ∈ fixV Y := by
    intro x hx y hy
    have := congrArg (fun g : MulAut V => g x) (hc y hy)
    simp only [MulAut.mul_apply] at this
    rw [← this, mem_fixV.mp hx y hy]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨z, hz, v, rfl⟩
  rcases mem_zpowers_sq ht hz with h | h
  · rw [h]; simp
  · rw [h]
    have hv : v ∈ commV Y ⊔ fixV Y := by rw [hsplit]; trivial
    obtain ⟨e, he, x, hx, rfl⟩ := Subgroup.mem_sup.mp hv
    have h1 : t (e * x) * (e * x)⁻¹ = t x * x⁻¹ := by
      rw [map_mul, htE e he, mul_inv_rev]
      calc e * t x * (x⁻¹ * e⁻¹) = (t x * x⁻¹) * (e * e⁻¹) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
        _ = t x * x⁻¹ := by rw [mul_inv_cancel, mul_one]
    rw [h1]
    exact mul_mem (htC x hx) (inv_mem hx)

private theorem commV_invariant_of_normalizing {Y : Subgroup (MulAut V)} {c : MulAut V}
    (hnorm : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) {w : V} (hw : w ∈ commV Y) : c w ∈ commV Y :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hnorm hw

theorem centralizes_of_fix_commV {Y : Subgroup (MulAut V)}
    (hsplit : commV Y ⊔ fixV Y = ⊤) {c : MulAut V} (hnorm : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    (hE : ∀ e ∈ commV Y, c e = e) : ∀ y ∈ Y, c * y = y * c := by
  intro y hy
  have hy' := hnorm y hy
  have hcinv : ∀ e ∈ commV Y, c⁻¹ e = e := fun e he => by
    have := congrArg (fun v : V => c⁻¹ v) (hE e he)
    simpa using this.symm
  have heq : c * y * c⁻¹ = y := by
    ext v
    have hv : v ∈ commV Y ⊔ fixV Y := by rw [hsplit]; trivial
    obtain ⟨e, he, x, hx, rfl⟩ := Subgroup.mem_sup.mp hv
    have h1 : (c * y * c⁻¹) (e * x) = (c * y * c⁻¹) e * x := by
      rw [map_mul, mem_fixV.mp hx _ hy']
    have h2 : (c * y * c⁻¹) e = y e := by
      simp only [MulAut.mul_apply]
      rw [hcinv e he, hE _ (commV_invariant hy he)]
    rw [h1, h2, map_mul, mem_fixV.mp hx y hy]
  have := congrArg (fun g : MulAut V => g * c) heq
  simpa [mul_assoc] using this

end Module

section Context

private theorem comp_eq_or_commute' {Γ : Type} [Group Γ] [Finite Γ] {t : Γ} {Y' : Subgroup Γ}
    (hY : IsComponentOf Y' (Subgroup.centralizer ({t} : Set Γ))) {d : Γ}
    (hd : d ∈ Subgroup.centralizer ({t} : Set Γ)) :
    Y'.map (MulAut.conj d).toMonoidHom = Y' ∨
      ⁅Y'.map (MulAut.conj d).toMonoidHom, Y'⁆ = ⊥ := by
  have hY := (ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hY
  have hdt : d * t * d⁻¹ = t := by
    rw [← Subgroup.mem_centralizer_iff.1 hd t rfl, mul_inv_cancel_right]
  have hC := LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton d t
  rw [hdt] at hC
  have hYd := LocalAnalysis.ComponentInitial.isComponentOf_map_conj hY d
  rw [hC] at hYd
  exact LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hYd hY

private theorem exists_comm_involutions (m : ℕ) (hm : 6 ≤ m) :
    ∃ a₁ a₂ : alternatingGroup (Fin m), a₁ ^ 2 = 1 ∧ a₂ ^ 2 = 1 ∧ a₁ ≠ 1 ∧ a₂ ≠ 1 ∧
      a₁ ≠ a₂ ∧ a₁ * a₂ = a₂ * a₁ := by
  have hcomm : ∀ {a b c d : Fin m}, a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      Commute (swap a b) (swap c d) := by
    intro a b c d hac had hbc hbd
    have : (swap a b).Disjoint (swap c d) := by
      intro x
      by_cases hx : x = a ∨ x = b
      · right
        apply swap_apply_of_ne_of_ne
        · rcases hx with rfl | rfl <;> assumption
        · rcases hx with rfl | rfl <;> assumption
      · left
        simp only [not_or] at hx
        exact swap_apply_of_ne_of_ne hx.1 hx.2
    exact this.commute
  let p : ℕ → Fin m := fun i => if h : i < m then ⟨i, h⟩ else ⟨0, by omega⟩
  have hp : ∀ i j, i < m → j < m → i ≠ j → p i ≠ p j := fun i j hi hj hij h => by
    simp only [p, hi, hj, dite_true, Fin.mk.injEq] at h
    exact hij h
  have h01 := hp 0 1 (by omega) (by omega) (by omega)
  have h23 := hp 2 3 (by omega) (by omega) (by omega)
  have h45 := hp 4 5 (by omega) (by omega) (by omega)
  have hsq : ∀ {a b : Fin m}, a ≠ b → swap a b * swap a b = 1 := fun _ => swap_mul_self _ _
  have c01_23 := hcomm (a := p 0) (b := p 1) (c := p 2) (d := p 3) (hp 0 2 (by omega) (by omega)
    (by omega)) (hp 0 3 (by omega) (by omega) (by omega)) (hp 1 2 (by omega) (by omega) (by omega))
    (hp 1 3 (by omega) (by omega) (by omega))
  have c01_45 := hcomm (a := p 0) (b := p 1) (c := p 4) (d := p 5) (hp 0 4 (by omega) (by omega)
    (by omega)) (hp 0 5 (by omega) (by omega) (by omega)) (hp 1 4 (by omega) (by omega) (by omega))
    (hp 1 5 (by omega) (by omega) (by omega))
  have c23_45 := hcomm (a := p 2) (b := p 3) (c := p 4) (d := p 5) (hp 2 4 (by omega) (by omega)
    (by omega)) (hp 2 5 (by omega) (by omega) (by omega)) (hp 3 4 (by omega) (by omega) (by omega))
    (hp 3 5 (by omega) (by omega) (by omega))
  have mem1 : swap (p 0) (p 1) * swap (p 2) (p 3) ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h23]
    decide
  have mem2 : swap (p 0) (p 1) * swap (p 4) (p 5) ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h45]
    decide
  refine ⟨⟨_, mem1⟩, ⟨_, mem2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (swap (p 0) (p 1) * swap (p 2) (p 3)) ^ 2 = 1
    rw [c01_23.mul_pow, pow_two, pow_two, hsq h01, hsq h23, mul_one]
  · apply Subtype.ext
    show (swap (p 0) (p 1) * swap (p 4) (p 5)) ^ 2 = 1
    rw [c01_45.mul_pow, pow_two, pow_two, hsq h01, hsq h45, mul_one]
  · intro h
    have := congrArg (fun f : alternatingGroup (Fin m) => (f : Perm (Fin m)) (p 0)) h
    simp only [Perm.mul_apply, OneMemClass.coe_one, Perm.coe_one, id_eq] at this
    rw [swap_apply_of_ne_of_ne (hp 0 2 (by omega) (by omega) (by omega))
      (hp 0 3 (by omega) (by omega) (by omega)), swap_apply_left] at this
    exact h01 this.symm
  · intro h
    have := congrArg (fun f : alternatingGroup (Fin m) => (f : Perm (Fin m)) (p 0)) h
    simp only [Perm.mul_apply, OneMemClass.coe_one, Perm.coe_one, id_eq] at this
    rw [swap_apply_of_ne_of_ne (hp 0 4 (by omega) (by omega) (by omega))
      (hp 0 5 (by omega) (by omega) (by omega)), swap_apply_left] at this
    exact h01 this.symm
  · intro h
    have := congrArg (fun f : alternatingGroup (Fin m) => (f : Perm (Fin m)) (p 2)) h
    simp only [Perm.mul_apply] at this
    rw [swap_apply_left, swap_apply_of_ne_of_ne (hp 2 4 (by omega) (by omega) (by omega))
      (hp 2 5 (by omega) (by omega) (by omega)),
      swap_apply_of_ne_of_ne (hp 2 0 (by omega) (by omega) (by omega))
        (hp 2 1 (by omega) (by omega) (by omega)),
      swap_apply_of_ne_of_ne (hp 3 0 (by omega) (by omega) (by omega))
        (hp 3 1 (by omega) (by omega) (by omega))] at this
    exact h23.symm this
  · apply Subtype.ext
    show (swap (p 0) (p 1) * swap (p 2) (p 3)) * (swap (p 0) (p 1) * swap (p 4) (p 5)) =
      (swap (p 0) (p 1) * swap (p 4) (p 5)) * (swap (p 0) (p 1) * swap (p 2) (p 3))
    exact ((Commute.refl (swap (p 0) (p 1))).mul_right c01_45 |>.mul_left
      (c01_23.symm.mul_right c23_45 |>.symm.symm)).eq

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem EndCfg4.normalizes_of_commute (h2 : Alt2Rank1) (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) {t c : ↥G}
    (ht : orderOf t = 2) (htY : (t : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)))
    (hct : c * t = t * c) :
    ∀ y ∈ Y, (c : MulAut V) * y * (c : MulAut V)⁻¹ ∈ Y := by
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hcomp := h.isComponentOf hm hY ht htY
  have hcC : c ∈ Subgroup.centralizer ({t} : Set ↥G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hct.symm
  rcases comp_eq_or_commute' hcomp hcC with heq | hcomm
  · intro y hy
    have hy' : (⟨y, hYG hy⟩ : ↥G) ∈ Y.subgroupOf G := hy
    have : c * ⟨y, hYG hy⟩ * c⁻¹ ∈ (Y.subgroupOf G).map (MulAut.conj c).toMonoidHom :=
      ⟨_, hy', rfl⟩
    rw [heq] at this
    exact this
  · exfalso
    obtain ⟨ε⟩ := hY
    obtain ⟨a₁, a₂, ha1, ha2, ha1n, ha2n, ha12, hac⟩ := exists_comm_involutions m (by omega)
    obtain ⟨y₁, rfl⟩ := ε.surjective a₁
    obtain ⟨y₂, rfl⟩ := ε.surjective a₂
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hB : ∀ y : ↥Y, (c : MulAut V) * (y : MulAut V) * (c : MulAut V)⁻¹ ∈
        Subgroup.centralizer (Y : Set (MulAut V)) := by
      intro y
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : (⟨z, hYG hz⟩ : ↥G) ∈ Y.subgroupOf G := hz
      have hmem : c * ⟨y, hYG y.2⟩ * c⁻¹ ∈ (Y.subgroupOf G).map (MulAut.conj c).toMonoidHom :=
        ⟨_, show (⟨y, hYG y.2⟩ : ↥G) ∈ Y.subgroupOf G from y.2, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp (hcen hmem) _ hz'
      exact congrArg Subtype.val this
    have hpow : ∀ y : ↥Y, (y : MulAut V) ^ 2 = 1 → ((c : MulAut V) * (y : MulAut V) *
        (c : MulAut V)⁻¹) ^ 2 = 1 := by
      intro y hy
      rw [conj_pow, hy]
      group
    refine h2 V hV G T Y h m hm hodd ⟨ε⟩ ((c : MulAut V) * (y₁ : MulAut V) * (c : MulAut V)⁻¹)
      ((c : MulAut V) * (y₂ : MulAut V) * (c : MulAut V)⁻¹) ?_ ?_ (hB y₁) (hB y₂)
      (hpow y₁ ?_) (hpow y₂ ?_) ?_ ?_ ?_ ?_
    · exact G.mul_mem (G.mul_mem c.2 (hYG y₁.2)) (G.inv_mem c.2)
    · exact G.mul_mem (G.mul_mem c.2 (hYG y₂.2)) (G.inv_mem c.2)
    · have h : y₁ ^ 2 = 1 := ε.injective (by rw [map_pow, ha1, map_one])
      rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
    · have h : y₂ ^ 2 = 1 := ε.injective (by rw [map_pow, ha2, map_one])
      rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
    · intro hB1
      apply ha1n
      have : (y₁ : MulAut V) = 1 := by simpa using hB1
      have h1 : y₁ = 1 := Subtype.ext this
      rw [h1, map_one]
    · intro hB1
      apply ha2n
      have : (y₂ : MulAut V) = 1 := by simpa using hB1
      have h1 : y₂ = 1 := Subtype.ext this
      rw [h1, map_one]
    · intro hB1
      apply ha12
      have : (y₁ : MulAut V) = y₂ := by simpa using hB1
      have h1 : y₁ = y₂ := Subtype.ext this
      rw [h1]
    · have hy12 : y₁ * y₂ = y₂ * y₁ := ε.injective (by rw [map_mul, map_mul, hac])
      have : (y₁ : MulAut V) * y₂ = y₂ * y₁ := congrArg Subtype.val hy12
      calc (c : MulAut V) * y₁ * (c : MulAut V)⁻¹ * ((c : MulAut V) * y₂ * (c : MulAut V)⁻¹)
          = (c : MulAut V) * ((y₁ : MulAut V) * y₂) * (c : MulAut V)⁻¹ := by group
        _ = (c : MulAut V) * ((y₂ : MulAut V) * y₁) * (c : MulAut V)⁻¹ := by rw [this]
        _ = (c : MulAut V) * y₂ * (c : MulAut V)⁻¹ * ((c : MulAut V) * y₁ * (c : MulAut V)⁻¹) := by
          group

theorem EndCfg4.commV_ne (h2 : Alt2Rank1) (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) {t : ↥G} (ht : orderOf t = 2)
    (htY : (t : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V))) {c : ↥G}
    (hc : c ∈ cls t) (hct : c ≠ t) :
    commV (Subgroup.zpowers (t : MulAut V)) ≠ commV (Subgroup.zpowers (c : MulAut V)) := by
  intro heq
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  obtain ⟨θ₀, hnat⟩ := h.exists_natSection hV hm hodd hY
  have hsplit := commV_sup_fixV_of_natural hodd (by omega) θ₀ hnat
  have hEC := commV_inf_fixV_of_natural hodd (by omega) θ₀ hnat
  have hc2' : orderOf c = 2 := CFSG.EvenSmallLie.OddTranspAlt.orderOf_of_mem_cls_of ht hc
  have sq : ∀ x : ↥G, orderOf x = 2 → (x : MulAut V) ^ 2 = 1 := by
    intro x hx
    have h1 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have ht2 := sq t ht
  have hc2 := sq c hc2'
  have hcomm' : (t : MulAut V) * c = c * t := commute_of_commV_eq hV ht2 hc2 heq
  have hcomm : c * t = t * c := Subtype.ext hcomm'.symm
  have hP1 := commV_zpowers_le_fixV hV hm hodd θ₀ hnat ht2
    (fun y hy => (Subgroup.mem_centralizer_iff.mp htY y hy).symm)
  have hnorm := h.normalizes_of_commute h2 hV hm hodd hY ht htY hcomm
  have hnt : ∃ e ∈ commV Y, (c : MulAut V) e ≠ e := by
    by_contra hcon
    push Not at hcon
    have hcent := centralizes_of_fix_commV hsplit hnorm hcon
    refine h2 V hV G T Y h m hm hodd hY (t : MulAut V) (c : MulAut V) t.2 c.2 htY ?_ ht2 hc2 ?_ ?_
      ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      exact fun y hy => (hcent y hy).symm
    · intro h1
      have : t = 1 := Subtype.ext h1
      rw [this] at ht
      simp at ht
    · intro h1
      have : c = 1 := Subtype.ext h1
      rw [this] at hc2'
      simp at hc2'
    · intro h1
      exact hct (Subtype.ext h1.symm)
    · exact hcomm'
  obtain ⟨e, he, hce⟩ := hnt
  have hw1 : (c : MulAut V) e * e⁻¹ ∈ commV (Subgroup.zpowers (c : MulAut V)) :=
    Subgroup.subset_closure ⟨(c : MulAut V), Subgroup.mem_zpowers _, e, rfl⟩
  have hw2 : (c : MulAut V) e * e⁻¹ ∈ fixV Y := hP1 (heq ▸ hw1)
  have hw3 : (c : MulAut V) e * e⁻¹ ∈ commV Y :=
    mul_mem (commV_invariant_of_normalizing hnorm he) (inv_mem he)
  have h5 : (c : MulAut V) e * e⁻¹ ∈ commV Y ⊓ fixV Y := ⟨hw3, hw2⟩
  rw [hEC, Subgroup.mem_bot, mul_inv_eq_one] at h5
  exact hce h5

theorem alt419_of_card_two (h2 : Alt2Rank1) (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) {t : ↥G} (ht : orderOf t = 2)
    (htT : (t : MulAut V) ∈ T) (hr : Nat.card ↥(commV (Subgroup.zpowers (t : MulAut V))) = 2)
    (x : ↥G) (hx : x ∈ cls t) (y : ↥G) (hy : y ∈ cls t) :
    Odd (orderOf (x * y)) ∨ orderOf (x * y) = 2 := by
  have htY : (t : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (h.adm.hYC hz).2 (t : MulAut V) htT).symm
  have sq : ∀ c ∈ cls t, (c : MulAut V) ^ 2 = 1 := by
    intro c hc
    have h2' : orderOf c = 2 := CFSG.EvenSmallLie.OddTranspAlt.orderOf_of_mem_cls_of ht hc
    have h3 : c ^ 2 = 1 := by rw [← h2']; exact pow_orderOf_eq_one c
    rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  let 𝒞 : Set (MulAut V) := {z | ∃ c ∈ cls t, (c : MulAut V) = z}
  have hcardc : ∀ c ∈ cls t, Nat.card ↥(commV (Subgroup.zpowers (c : MulAut V))) = 2 := by
    intro c hc
    obtain ⟨e, rfl⟩ := hc
    have : ((e * t * e⁻¹ : ↥G) : MulAut V) =
        (e : MulAut V) * (t : MulAut V) * (e : MulAut V)⁻¹ := rfl
    rw [this, commV_zpowers_conj, Subgroup.card_map_of_injective (e : MulAut V).injective]
    exact hr
  have hbound := orderOf_mul_le_three (𝒞 := 𝒞) (a := (x : MulAut V)) (b := (y : MulAut V))
    ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (sq x hx) (sq y hy) ?_ ?_ ?_
  · have h3 : orderOf (x * y) ≤ 3 := by
      rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
      exact hbound
    have hpos : 0 < orderOf (x * y) := orderOf_pos _
    have : orderOf (x * y) = 1 ∨ orderOf (x * y) = 2 ∨ orderOf (x * y) = 3 := by omega
    rcases this with h4 | h4 | h4
    · left; rw [h4]; exact odd_one
    · right; exact h4
    · left; rw [h4]; exact ⟨1, rfl⟩
  · rintro _ ⟨c, hc, rfl⟩ g hg
    have hgG : g ∈ G := by
      refine (Subgroup.closure_le G).mpr ?_ hg
      rintro z (rfl | rfl)
      · exact x.2
      · exact y.2
    exact ⟨⟨g, hgG⟩ * c * ⟨g, hgG⟩⁻¹, CFSG.EvenSmallLie.OddTranspAlt.conj_mem_cls hc _, rfl⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hcardc c hc
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hne heq
    obtain ⟨e, rfl⟩ := hc
    have hc'' : e⁻¹ * c' * e ∈ cls t := by
      have := CFSG.EvenSmallLie.OddTranspAlt.conj_mem_cls hc' e⁻¹
      simpa using this
    have hne'' : e⁻¹ * c' * e ≠ t := by
      intro h3
      apply hne
      have : c' = e * t * e⁻¹ := by
        calc c' = e * (e⁻¹ * c' * e) * e⁻¹ := by group
          _ = e * t * e⁻¹ := by rw [h3]
      rw [this]
    refine h.commV_ne h2 hV hm hodd hY ht htY hc'' hne'' ?_
    have hcc : (c' : MulAut V) = (e : MulAut V) * ((e⁻¹ * c' * e : ↥G) : MulAut V) *
        (e : MulAut V)⁻¹ := by
      have : c' = e * (e⁻¹ * c' * e) * e⁻¹ := by group
      conv_lhs => rw [this]
      rfl
    have hcc0 : ((e * t * e⁻¹ : ↥G) : MulAut V) =
        (e : MulAut V) * (t : MulAut V) * (e : MulAut V)⁻¹ := rfl
    rw [hcc0, commV_zpowers_conj] at heq
    rw [hcc, commV_zpowers_conj] at heq
    exact Subgroup.map_injective (e : MulAut V).injective heq

end Context

end CFSG.CGT.PushingUpLit.CGT6
