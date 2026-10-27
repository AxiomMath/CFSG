module

public import CFSG.GH74.GLS.Stage2.Signalizer.L48AltCfg
public import CFSG.GH74.Uniqueness.SU.SU13TA1Class
public import CFSG.GH74.Uniqueness.SU.SU13TA2Cent
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Equiv Equiv.Perm Subgroup

section Core

open CFSG.GH74.Uniqueness.SU.SU13.TA

variable {K : Type} [Group K] {n : ℕ} {π : K →* alternatingGroup (Fin n)}

abbrev pm (π : K →* alternatingGroup (Fin n)) (x : K) : Perm (Fin n) := ((π x : alternatingGroup (Fin n)) : Perm (Fin n))

theorem pm_mul (x y : K) : pm π (x * y) = pm π x * pm π y := by simp [pm]

theorem sq_of_mem {R : Subgroup (Perm (Fin n))} {B : Set (Fin n)} (hc : AltConfig n R B) (hn8 : 8 ≤ n)
    (hπ : TwoCover π) {x : K} (hx : pm π x ∈ R) : x * x = 1 := by
  by_cases h1 : pm π x = 1
  · have : x ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    simpa [pow_two] using hπ.sq_eq_one_of_mem_ker' this
  · have := hπ.sq_eq_one_of_cycleType_two_two_two_two hn8 (hc.cyc _ hx h1)
    simpa [pow_two] using this

theorem comm_of_mem {R : Subgroup (Perm (Fin n))} {B : Set (Fin n)} (hc : AltConfig n R B) (hn8 : 8 ≤ n)
    (hπ : TwoCover π) {x y : K} (hx : pm π x ∈ R) (hy : pm π y ∈ R) : x * y = y * x := by
  have hx2 := sq_of_mem hc hn8 hπ hx
  have hy2 := sq_of_mem hc hn8 hπ hy
  have hxy2 := sq_of_mem hc hn8 hπ (x := x * y) (by rw [pm_mul]; exact R.mul_mem hx hy)
  have e1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have e2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have e3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy2
  calc x * y = (x * y)⁻¹ := e3.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [e1, e2]

open scoped IsMulCommutative

theorem perm_apply_inv_self {α : Type*} (ρ : Perm α) (x : α) : ρ (ρ⁻¹ x) = x := by
  rw [← Perm.mul_apply, mul_inv_cancel]
  rfl

@[expose] def conjAction {Γ : Type*} [Group Γ] (R Yb : Subgroup Γ) (h : ∀ ρ ∈ R, ∀ σ ∈ Yb, ρ * σ * ρ⁻¹ ∈ Yb) :
    ↥R →* MulAut ↥Yb where
  toFun ρ :=
    { toFun := fun y => ⟨(ρ : Γ) * y * (ρ : Γ)⁻¹, h ρ ρ.2 y y.2⟩
      invFun := fun y => ⟨(ρ : Γ)⁻¹ * y * (ρ : Γ), by
        have := h (ρ⁻¹) (R.inv_mem ρ.2) y y.2
        simpa using this⟩
      left_inv := fun y => by ext; simp [mul_assoc]
      right_inv := fun y => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp [mul_assoc]

theorem core_twoAlt [Finite K] (hn8 : 8 ≤ n) (hπ : TwoCover π) {R : Subgroup (Perm (Fin n))} {B : Set (Fin n)}
    (hc : AltConfig n R B) {t₀ : K} (ht₀R : pm π t₀ ∈ R) (ht₀1 : pm π t₀ ≠ 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup K} (hY : IsPGroup p ↥Y)
    (hN : ∀ c : K, c * t₀ = t₀ * c → c ∈ normalizer (Y : Set K)) (hcomm : ⁅Y, zpowers t₀⁆ = Y) : Y = ⊥ := by
  classical
  have hRalt : ∀ ρ ∈ R, ρ ∈ alternatingGroup (Fin n) := fun ρ hρ => hc.mem_alt hρ
  have hlift : ∀ ρ ∈ R, ∃ x : K, pm π x = ρ := by
    intro ρ hρ
    obtain ⟨x, hx⟩ := hπ.surj ⟨ρ, hRalt ρ hρ⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  have hRN_lift : ∀ x : K, pm π x ∈ R → x ∈ normalizer (Y : Set K) := fun x hx =>
    hN x (comm_of_mem hc hn8 hπ hx ht₀R)
  let Yb : Subgroup (Perm (Fin n)) := Y.map ((alternatingGroup (Fin n)).subtype.comp π)
  have hmemYb : ∀ σ, σ ∈ Yb ↔ ∃ y ∈ Y, pm π y = σ := fun σ => by
    simp [Yb, Subgroup.mem_map, pm]
  have hRN : ∀ ρ ∈ R, ∀ σ ∈ Yb, ρ * σ * ρ⁻¹ ∈ Yb := by
    intro ρ hρ σ hσ
    obtain ⟨y, hy, rfl⟩ := (hmemYb σ).mp hσ
    obtain ⟨x, rfl⟩ := hlift ρ hρ
    have hxN := hRN_lift x hρ
    have : x * y * x⁻¹ ∈ Y := (mem_normalizer_iff.mp hxN y).mp hy
    refine (hmemYb _).mpr ⟨x * y * x⁻¹, this, ?_⟩
    simp [pm]
  have hRsq : ∀ ρ ∈ R, ρ * ρ = 1 := by
    intro ρ hρ
    obtain ⟨x, rfl⟩ := hlift ρ hρ
    rw [← pm_mul, sq_of_mem hc hn8 hπ hρ]
    simp [pm]
  have hRcomm : ∀ ρ ∈ R, ∀ σ ∈ R, ρ * σ = σ * ρ := by
    intro ρ hρ σ hσ
    obtain ⟨x, rfl⟩ := hlift ρ hρ
    obtain ⟨y, rfl⟩ := hlift σ hσ
    rw [← pm_mul, ← pm_mul, comm_of_mem hc hn8 hπ hρ hσ]
  have hIsComm : IsMulCommutative ↥R := ⟨⟨fun a b => Subtype.ext (hRcomm a a.2 b b.2)⟩⟩
  have hncyc : ¬ IsCyclic ↥R := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hg2 : g * g = 1 := Subtype.ext (hRsq g g.2)
    have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hg2)
    have hcard : Nat.card ↥R = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    have h8 := hc.card_R
    have := Nat.le_of_dvd (by norm_num) hord
    omega
  have hR2 : IsPGroup 2 ↥R := fun g => ⟨1, by
    have : g * g = 1 := Subtype.ext (hRsq g g.2)
    simpa [pow_two] using this⟩
  have : Fact (IsPGroup 2 ↥R) := ⟨hR2⟩
  have hpf : Fact p.Prime := ⟨hp⟩
  have hYbp : IsPGroup p ↥Yb := hY.map _
  have hcop : Nat.Coprime 2 (Nat.card ↥Yb) := by
    obtain ⟨k, hk⟩ := hYbp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  let _inst : MulDistribMulAction ↥R ↥Yb :=
    MulDistribMulAction.compHom ↥Yb (conjAction R Yb hRN)
  have hact : ∀ (ρ : ↥R) (y : ↥Yb), ((ρ • y : ↥Yb) : Perm (Fin n)) = (ρ : Perm (Fin n)) * y * (ρ : Perm (Fin n))⁻¹ :=
    fun ρ y => rfl
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := ↥Yb) (A := ↥R) 2 hcop hncyc
  let stab : Subgroup (Perm (Fin n)) :=
    { carrier := {σ | ∀ x, σ x ∈ B ↔ x ∈ B}
      mul_mem' := fun {a b} ha hb x => by
        show a (b x) ∈ B ↔ x ∈ B
        rw [ha, hb]
      one_mem' := fun x => Iff.rfl
      inv_mem' := fun {a} ha x => by
        have h1 := ha (a⁻¹ x)
        have h2 : a (a⁻¹ x) = x := perm_apply_inv_self a x
        rw [h2] at h1
        exact h1.symm }
  have hpres : ∀ σ ∈ Yb, ∀ x, σ x ∈ B ↔ x ∈ B := by
    have htop : (⊤ : Subgroup ↥Yb) ≤ stab.comap Yb.subtype := by
      rw [← hgen]
      refine iSup₂_le fun a ha g hg => ?_
      have h1 : ((⟨a, Subgroup.mem_zpowers a⟩ : ↥(zpowers a)) • g : ↥Yb) = g :=
        (FixedPoints.mem_subgroup _ _ g).mp hg ⟨a, Subgroup.mem_zpowers a⟩
      set gP : Perm (Fin n) := (g : Perm (Fin n)) with hgP
      have h2 : (a : Perm (Fin n)) * gP * (a : Perm (Fin n))⁻¹ = gP := congrArg Subtype.val h1
      have hne : (a : Perm (Fin n)) ≠ 1 := fun h => ha (Subtype.ext h)
      have hsupp := hc.supp a a.2 hne
      have h3 : (a : Perm (Fin n)) * gP = gP * a := by
        calc (a : Perm (Fin n)) * gP = ((a : Perm (Fin n)) * gP * (a : Perm (Fin n))⁻¹) * a := by group
          _ = gP * a := by rw [h2]
      have hcomm' : ∀ x, (a : Perm (Fin n)) (gP x) = gP ((a : Perm (Fin n)) x) := fun x =>
        congrArg (fun f : Perm (Fin n) => f x) h3
      show ∀ x, gP x ∈ B ↔ x ∈ B
      intro x
      rw [← hsupp, ← hsupp, hcomm' x]
      exact gP.injective.ne_iff
    intro σ hσ
    exact htop (Subgroup.mem_top (⟨σ, hσ⟩ : ↥Yb))
  let act : ↥Yb →* Perm ↥B :=
    { toFun := fun y => Equiv.Perm.subtypePerm (y : Perm (Fin n)) (fun x => hpres y y.2 x)
      map_one' := by ext; rfl
      map_mul' := fun a b => by ext; rfl }
  let _instB : MulAction ↥Yb ↥B := MulAction.compHom ↥B act
  have hBcard : ¬ p ∣ Nat.card ↥B := by
    rw [hc.card_B]
    intro h
    have h8 : p ∣ 2 ^ 3 := by norm_num; exact h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h8))
  obtain ⟨b₀, hb₀⟩ := hYbp.nonempty_fixed_point_of_prime_not_dvd_card ↥B hBcard
  have hb₀' : ∀ σ ∈ Yb, σ (b₀ : Fin n) = b₀ := by
    intro σ hσ
    have := (MulAction.mem_fixedPoints.mp hb₀) ⟨σ, hσ⟩
    exact congrArg Subtype.val this
  have hfix : ∀ σ ∈ Yb, ∀ b ∈ B, σ b = b := by
    intro σ hσ b hb
    obtain ⟨ρ, hρ, hρb⟩ := hc.trans b₀ b₀.2 b hb
    have h1 : (ρ⁻¹ * σ * ρ) ∈ Yb := by
      have := hRN (ρ⁻¹) (R.inv_mem hρ) σ hσ
      simpa using this
    have h2 := hb₀' _ h1
    have h3 : ρ⁻¹ (σ (ρ b₀)) = b₀ := by simpa [Perm.mul_apply] using h2
    have h4 : σ (ρ b₀) = ρ b₀ := by
      calc σ (ρ b₀) = ρ (ρ⁻¹ (σ (ρ b₀))) := (perm_apply_inv_self ρ _).symm
        _ = ρ b₀ := by rw [h3]
    rw [← hρb]
    exact h4
  have hτsq : pm π t₀ * pm π t₀ = 1 := hRsq _ ht₀R
  have hcommτ : ∀ σ ∈ Yb, σ * pm π t₀ = pm π t₀ * σ := by
    intro σ hσ
    ext x
    rw [Perm.mul_apply, Perm.mul_apply]
    by_cases hx : x ∈ B
    · have h1 : σ x = x := hfix σ hσ x hx
      have hx1 : pm π t₀ x ≠ x := (hc.supp _ ht₀R ht₀1 x).mpr hx
      have h2 : pm π t₀ x ∈ B := by
        rw [← hc.supp _ ht₀R ht₀1]
        have : pm π t₀ (pm π t₀ x) = x := by
          have := congrArg (fun f : Perm (Fin n) => f x) hτsq
          simpa [Perm.mul_apply] using this
        rw [this]
        exact fun h => hx1 h.symm
      rw [h1, hfix σ hσ _ h2]
    · have hτx : pm π t₀ x = x := by
        by_contra h
        exact hx ((hc.supp _ ht₀R ht₀1 x).mp h)
      have hsx : σ x ∉ B := by
        intro hb
        have h1 := hfix σ hσ _ hb
        have h2 := σ.injective h1
        rw [h2] at hb
        exact hx hb
      have hτsx : pm π t₀ (σ x) = σ x := by
        by_contra h
        exact hsx ((hc.supp _ ht₀R ht₀1 (σ x)).mp h)
      rw [hτx, hτsx]
  have hyc : ∀ y ∈ Y, t₀ * y = y * t₀ := by
    intro y hy
    have hodd : Odd (orderOf y) := by
      obtain ⟨k, hk⟩ := hY ⟨y, hy⟩
      have hk' : y ^ p ^ k = 1 := congrArg Subtype.val hk
      exact Odd.of_dvd_nat (Odd.pow (hp.odd_of_ne_two hp2)) (orderOf_dvd_of_pow_eq_one hk')
    have hσ : pm π y ∈ Yb := (hmemYb _).mpr ⟨y, hy, rfl⟩
    have hcP : pm π y * pm π t₀ = pm π t₀ * pm π y := hcommτ _ hσ
    have hcA : Commute (π t₀) (π y) := Subtype.ext hcP.symm
    exact (hπ.commute_of_odd_orderOf hodd hcA).eq
  have hbot : ⁅Y, zpowers t₀⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (hyc y hy : Commute t₀ y) m)).eq
  rw [← hcomm, hbot]

end Core

theorem mem_map_conj_inv {K : Type} [Group K] (Y : Subgroup K) (c x : K) :
    x ∈ Y.map (MulAut.conj c⁻¹).toMonoidHom ↔ c * x * c⁻¹ ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨c * x * c⁻¹, hx, by simp [mul_assoc]⟩

section Main

open CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.GLS

open scoped commutatorElement

theorem star_twoAlt {K : Type} [Group K] [Finite K] {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hK : IsDoubleCoverOfAlt K n) (t : K) (ht2 : t * t = 1) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (Y : Subgroup K) (hY : IsPGroup p ↥Y)
    (hN : ∀ c : K, c * t = t * c → c ∈ normalizer (Y : Set K))
    (hc : ⁅Y, zpowers t⁆ = Y) : Y = ⊥ := by
  classical
  have hT : CFSG.GH74.Uniqueness.SU.K.IsTwoAlt K n :=
    ⟨hK.1, (inferInstance : Finite K), hK.2.1, hK.2.2⟩
  obtain ⟨π, hπ⟩ := TwoCover.exists_of_isTwoAlt hT
  by_cases ht1 : t = 1
  · subst ht1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right] at hc
    exact hc.symm
  by_cases htk : t ∈ π.ker
  ·
    have hcen : t ∈ center K := hπ.ker_le_center htk
    have hbot : ⁅Y, zpowers t⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine Subgroup.commutator_le.mpr fun y _ w hw => ?_
      have hwc : w ∈ center K := Subgroup.zpowers_le.mpr hcen hw
      have : y * w = w * y := Subgroup.mem_center_iff.mp hwc y
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact this
    rw [← hc, hbot]
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  obtain ⟨R, B, hcfg⟩ := exists_altConfig hn8
  have hRne : R ≠ ⊥ := by
    intro hR
    have h8 := hcfg.card_R
    rw [hR, Subgroup.card_bot] at h8
    omega
  obtain ⟨ρ₀, hρ₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hRne
  have hρ₀R : (ρ₀ : Perm (Fin n)) ∈ R := ρ₀.2
  have hρ₀1' : (ρ₀ : Perm (Fin n)) ≠ 1 := fun h => hρ₀1 (Subtype.ext h)
  obtain ⟨t₀, ht₀⟩ := hπ.surj ⟨(ρ₀ : Perm (Fin n)), hcfg.mem_alt hρ₀R⟩
  have ht₀pm : pm π t₀ = ρ₀ := congrArg Subtype.val ht₀
  have ht₀R : pm π t₀ ∈ R := by rw [ht₀pm]; exact hρ₀R
  have ht₀1 : pm π t₀ ≠ 1 := by rw [ht₀pm]; exact hρ₀1'
  obtain ⟨ht₀o, ht₀k⟩ := hπ.orderOf_eq_two_of_cycleType_two_two_two_two hn8
    (x := t₀) (hcfg.cyc _ ht₀R ht₀1)
  obtain ⟨c, hct⟩ := isConj_iff.mp (hπ.isConj_of_orderOf_eq_two hn8 hn11 ht₀o hto ht₀k htk)
  set φ : K ≃* K := MulAut.conj c⁻¹ with hφ
  have hφx : ∀ x, φ x = c⁻¹ * x * c := fun x => by simp [hφ]
  have hφt : φ t = t₀ := by rw [hφx, ← hct]; group
  set Y₀ : Subgroup K := Y.map φ.toMonoidHom with hY₀
  have hmem : ∀ x, x ∈ Y₀ ↔ c * x * c⁻¹ ∈ Y := fun x => mem_map_conj_inv Y c x
  have hY₀p : IsPGroup p ↥Y₀ := hY.map _
  have hN₀ : ∀ d : K, d * t₀ = t₀ * d → d ∈ normalizer (Y₀ : Set K) := by
    intro d hd
    have hd' : (c * d * c⁻¹) * t = t * (c * d * c⁻¹) := by
      rw [← hct]
      calc c * d * c⁻¹ * (c * t₀ * c⁻¹) = c * (d * t₀) * c⁻¹ := by group
        _ = c * (t₀ * d) * c⁻¹ := by rw [hd]
        _ = c * t₀ * c⁻¹ * (c * d * c⁻¹) := by group
    have h1 := hN _ hd'
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro y
    rw [hmem, hmem]
    have := h1 (c * y * c⁻¹)
    have e : c * d * c⁻¹ * (c * y * c⁻¹) * (c * d * c⁻¹)⁻¹ = c * (d * y * d⁻¹) * c⁻¹ := by group
    rwa [e] at this
  have hc₀ : ⁅Y₀, zpowers t₀⁆ = Y₀ := by
    have h1 : zpowers t₀ = (zpowers t).map φ.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp [hφt]
    rw [h1, hY₀, ← Subgroup.map_commutator, hc]
  have hbot₀ := core_twoAlt hn8 hπ hcfg ht₀R ht₀1 hp hp2 hY₀p hN₀ hc₀
  exact Subgroup.map_injective (f := φ.toMonoidHom) φ.injective (hbot₀.trans (Subgroup.map_bot _).symm)

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.L48
