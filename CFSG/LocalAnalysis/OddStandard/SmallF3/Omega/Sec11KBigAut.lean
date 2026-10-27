module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigC

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma conj_mem_of_mem_normalizer {X : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hx : x ∈ X) : g * x * g⁻¹ ∈ X :=
  ((Subgroup.mem_normalizer_iff (H := X)).mp hg x).mp hx

private lemma oddCore_inf_sylow_eq_bot [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X) :
    oddCoreIn X ⊓ P = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgO, hgP⟩ := hg
  have hcop : Nat.Coprime (Nat.card (oddCoreIn X)) (Nat.card P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP.2.1
    rw [hn]
    exact (sec11KB_oddCore_odd X).coprime_two_right.pow_right n
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    ((oddCoreIn X).orderOf_dvd_natCard hgO) (P.orderOf_dvd_natCard hgP))

private lemma sylow_mul_oddCore [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) :
    ∀ x ∈ X, ∃ o ∈ oddCoreIn X, ∃ p ∈ P, o * p = x := by
  have hPO : P ≤ Subgroup.normalizer (oddCoreIn X : Set G) := by
    rw [Subgroup.le_set_normalizer_iff]
    intro p hp o ho
    exact sec11KB_oddCore_norm X (hP.1 hp) ho
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (oddCoreIn X) P hPO
  rw [hXP] at hcoe
  intro x hx
  change x ∈ (X : Set G) at hx
  rw [hcoe, Set.mem_mul] at hx
  exact hx

private lemma oddCore_mul_sylow_unique [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    {o₁ o₂ p₁ p₂ : G} (ho₁ : o₁ ∈ oddCoreIn X) (ho₂ : o₂ ∈ oddCoreIn X)
    (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P) (heq : o₁ * p₁ = o₂ * p₂) :
    o₁ = o₂ ∧ p₁ = p₂ := by
  have hbot : oddCoreIn X ⊓ P = ⊥ := oddCore_inf_sylow_eq_bot hP
  have h3 : o₂⁻¹ * o₁ = p₂ * p₁⁻¹ := by
    have h2 : o₂⁻¹ * o₁ * p₁ = p₂ := by
      calc o₂⁻¹ * o₁ * p₁ = o₂⁻¹ * (o₁ * p₁) := by rw [mul_assoc]
        _ = o₂⁻¹ * (o₂ * p₂) := by rw [heq]
        _ = o₂⁻¹ * o₂ * p₂ := by rw [mul_assoc]
        _ = 1 * p₂ := by rw [inv_mul_cancel]
        _ = p₂ := by rw [one_mul]
    rw [← h2, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : o₂⁻¹ * o₁ ∈ oddCoreIn X ⊓ P := by
    rw [Subgroup.mem_inf]
    exact ⟨mul_mem (Subgroup.inv_mem (oddCoreIn X) ho₂) ho₁,
      by rw [h3]; exact mul_mem hp₂ (Subgroup.inv_mem P hp₁)⟩
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  refine ⟨hmem.symm, ?_⟩
  rw [hmem] at heq
  exact mul_left_cancel heq

private lemma exists_odd_mul_sylow [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) {x : G} (hx : x ∈ X) :
    ∃ q : G × G, q.1 ∈ oddCoreIn X ∧ q.2 ∈ P ∧ q.1 * q.2 = x := by
  obtain ⟨o, ho, p, hp, h⟩ := sylow_mul_oddCore hP hXP x hx
  exact ⟨(o, p), ho, hp, h⟩

private noncomputable def oddPart [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) (p : ↥P) : G :=
  (Classical.choose (exists_odd_mul_sylow hP hXP
    (conj_mem_of_mem_normalizer g.2 (hP.1 p.2)))).1

private noncomputable def sylowPart [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) (p : ↥P) : G :=
  (Classical.choose (exists_odd_mul_sylow hP hXP
    (conj_mem_of_mem_normalizer g.2 (hP.1 p.2)))).2

private lemma oddPart_mem [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) (p : ↥P) :
    oddPart hP hXP g p ∈ oddCoreIn X := by
  unfold oddPart
  exact (Classical.choose_spec (exists_odd_mul_sylow hP hXP
    (conj_mem_of_mem_normalizer g.2 (hP.1 p.2)))).1

private lemma sylowPart_mem [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) (p : ↥P) :
    sylowPart hP hXP g p ∈ P := by
  unfold sylowPart
  exact (Classical.choose_spec (exists_odd_mul_sylow hP hXP
    (conj_mem_of_mem_normalizer g.2 (hP.1 p.2)))).2.1

private lemma oddPart_mul_sylowPart [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) (p : ↥P) :
    oddPart hP hXP g p * sylowPart hP hXP g p = g * (p : G) * (g : G)⁻¹ := by
  unfold oddPart sylowPart
  exact (Classical.choose_spec (exists_odd_mul_sylow hP hXP
    (conj_mem_of_mem_normalizer g.2 (hP.1 p.2)))).2.2

private lemma sylowPart_one [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) :
    sylowPart hP hXP g 1 = 1 := by
  have h1 : (1 : G) * 1 = g * ((1 : ↥P) : G) * (g : G)⁻¹ := by simp
  have h2 := oddPart_mul_sylowPart hP hXP g 1
  have huniq := oddCore_mul_sylow_unique hP (one_mem (oddCoreIn X)) (oddPart_mem hP hXP g 1)
    (one_mem P) (sylowPart_mem hP hXP g 1) (h1.trans h2.symm)
  exact huniq.2.symm

private lemma sylowPart_mul [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) (p q : ↥P) :
    sylowPart hP hXP g (p * q) = sylowPart hP hXP g p * sylowPart hP hXP g q := by
  have hp' := oddPart_mul_sylowPart hP hXP g p
  have hq' := oddPart_mul_sylowPart hP hXP g q
  have hO : sylowPart hP hXP g p * oddPart hP hXP g q * (sylowPart hP hXP g p)⁻¹ ∈
      oddCoreIn X :=
    sec11KB_oddCore_norm X (hP.1 (sylowPart_mem hP hXP g p)) (oddPart_mem hP hXP g q)
  have hmemO : oddPart hP hXP g p *
      (sylowPart hP hXP g p * oddPart hP hXP g q * (sylowPart hP hXP g p)⁻¹) ∈
      oddCoreIn X :=
    mul_mem (oddPart_mem hP hXP g p) hO
  have hmemP : sylowPart hP hXP g p * sylowPart hP hXP g q ∈ P :=
    mul_mem (sylowPart_mem hP hXP g p) (sylowPart_mem hP hXP g q)
  have heq : (oddPart hP hXP g p *
        (sylowPart hP hXP g p * oddPart hP hXP g q * (sylowPart hP hXP g p)⁻¹)) *
        (sylowPart hP hXP g p * sylowPart hP hXP g q) =
      oddPart hP hXP g (p * q) * sylowPart hP hXP g (p * q) := by
    rw [oddPart_mul_sylowPart hP hXP g (p * q), Subgroup.coe_mul]
    calc (oddPart hP hXP g p *
          (sylowPart hP hXP g p * oddPart hP hXP g q * (sylowPart hP hXP g p)⁻¹)) *
          (sylowPart hP hXP g p * sylowPart hP hXP g q)
        = (oddPart hP hXP g p * sylowPart hP hXP g p) *
          (oddPart hP hXP g q * sylowPart hP hXP g q) := by group
      _ = (g * (p : G) * (g : G)⁻¹) * (g * (q : G) * (g : G)⁻¹) := by rw [hp', hq']
      _ = g * ((p : G) * (q : G)) * (g : G)⁻¹ := by group
  exact (oddCore_mul_sylow_unique hP hmemO (oddPart_mem hP hXP g (p * q)) hmemP
    (sylowPart_mem hP hXP g (p * q)) heq).2.symm

private noncomputable def sylowPartHom [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) : ↥P →* ↥P where
  toFun p := ⟨sylowPart hP hXP g p, sylowPart_mem hP hXP g p⟩
  map_one' := Subtype.ext (sylowPart_one hP hXP g)
  map_mul' p q := Subtype.ext (sylowPart_mul hP hXP g p q)

private lemma sylowPartHom_apply [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) (p : ↥P) :
    ((sylowPartHom hP hXP g p : ↥P) : G) = sylowPart hP hXP g p := rfl

private lemma sylowPartHom_injective [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) :
    Function.Injective (sylowPartHom hP hXP g) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro p hp
  rw [MonoidHom.mem_ker] at hp
  have hp1 : sylowPart hP hXP g p = 1 := by
    rw [← sylowPartHom_apply hP hXP g p]
    exact congrArg Subtype.val hp
  have hgp : g * (p : G) * (g : G)⁻¹ ∈ oddCoreIn X := by
    have h := oddPart_mul_sylowPart hP hXP g p
    rw [hp1, mul_one] at h
    rw [← h]
    exact oddPart_mem hP hXP g p
  have hpO : (p : G) ∈ oddCoreIn X := by
    have h := sec11KB_conj_oddCore (X := X) (h := (g : G)⁻¹) (Subgroup.inv_mem _ g.2) hgp
    rwa [show (g : G)⁻¹ * (g * (p : G) * (g : G)⁻¹) * ((g : G)⁻¹)⁻¹ = (p : G) by
      group] at h
  have hpbot : (p : G) ∈ oddCoreIn X ⊓ P := by
    rw [Subgroup.mem_inf]; exact ⟨hpO, p.2⟩
  rw [oddCore_inf_sylow_eq_bot hP, Subgroup.mem_bot] at hpbot
  exact Subtype.ext hpbot

private noncomputable def phiAuto [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) : MulAut ↥P :=
  MulEquiv.ofBijective (sylowPartHom hP hXP g)
    ⟨sylowPartHom_injective hP hXP g,
      Finite.injective_iff_surjective.mp (sylowPartHom_injective hP hXP g)⟩

private lemma phiAuto_apply [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (g : ↥(Subgroup.normalizer (X : Set G))) (p : ↥P) :
    ((phiAuto hP hXP g p : ↥P) : G) = sylowPart hP hXP g p := rfl

private lemma phiAuto_pow_spec [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) {h : G} (hh : h ∈ Subgroup.normalizer (X : Set G)) (p : ↥P) :
    ∀ j : ℕ, ∃ o ∈ oddCoreIn X,
      o * (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p : G) = h ^ j * (p : G) * (h ^ j)⁻¹ := by
  intro j
  induction j with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ j ih =>
      obtain ⟨o, ho, hoj⟩ := ih
      have hspec : oddPart hP hXP ⟨h, hh⟩ (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p) *
          sylowPart hP hXP ⟨h, hh⟩ (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p) =
          h * ((((phiAuto hP hXP ⟨h, hh⟩) ^ j) p : ↥P) : G) * h⁻¹ :=
        oddPart_mul_sylowPart hP hXP ⟨h, hh⟩ (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p)
      have hstep : (((phiAuto hP hXP ⟨h, hh⟩) ^ (j + 1)) p : G) =
          sylowPart hP hXP ⟨h, hh⟩ (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p) := by
        rw [pow_succ']
        rfl
      refine ⟨h * o * h⁻¹ * oddPart hP hXP ⟨h, hh⟩ (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p),
        mul_mem (sec11KB_conj_oddCore hh ho)
          (oddPart_mem hP hXP ⟨h, hh⟩ (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p)), ?_⟩
      rw [hstep]
      calc (h * o * h⁻¹ * oddPart hP hXP ⟨h, hh⟩ (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p)) *
            sylowPart hP hXP ⟨h, hh⟩ (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p)
          = h * o * h⁻¹ * (oddPart hP hXP ⟨h, hh⟩ (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p) *
              sylowPart hP hXP ⟨h, hh⟩ (((phiAuto hP hXP ⟨h, hh⟩) ^ j) p)) := by group
        _ = h * o * h⁻¹ *
              (h * ((((phiAuto hP hXP ⟨h, hh⟩) ^ j) p : ↥P) : G) * h⁻¹) := by rw [hspec]
        _ = h * (o * ((((phiAuto hP hXP ⟨h, hh⟩) ^ j) p : ↥P) : G)) * h⁻¹ := by group
        _ = h * (h ^ j * (p : G) * (h ^ j)⁻¹) * h⁻¹ := by rw [hoj]
        _ = h ^ (j + 1) * (p : G) * (h ^ (j + 1))⁻¹ := by group

private lemma phiAuto_pow_orderOf_eq_one [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) {h : G} (hh : h ∈ Subgroup.normalizer (X : Set G)) :
    phiAuto hP hXP ⟨h, hh⟩ ^ orderOf h = 1 := by
  ext p
  have hspec := phiAuto_pow_spec hP hXP hh p (orderOf h)
  obtain ⟨o, ho, hoj⟩ := hspec
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hoj
  have heq : (1 : G) * (p : G) = o *
      (((phiAuto hP hXP ⟨h, hh⟩ ^ orderOf h) p : ↥P) : G) := by
    rw [hoj, one_mul]
  have huniq := oddCore_mul_sylow_unique hP (one_mem (oddCoreIn X)) ho p.2
    ((phiAuto hP hXP ⟨h, hh⟩ ^ orderOf h) p).2 heq
  simpa using huniq.2.symm

private lemma conj_mem_oddCore_of_sylow [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (hAut : IsPGroup 2 (MulAut ↥P)) {h : G}
    (hh : h ∈ Subgroup.normalizer (X : Set G)) (hodd : Odd (orderOf h)) {p : G} (hp : p ∈ P) :
    h * p * h⁻¹ * p⁻¹ ∈ oddCoreIn X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : orderOf (phiAuto hP hXP ⟨h, hh⟩) ∣ orderOf h :=
    orderOf_dvd_of_pow_eq_one (phiAuto_pow_orderOf_eq_one hP hXP hh)
  have hcop : Nat.Coprime (orderOf (phiAuto hP hXP ⟨h, hh⟩)) (orderOf h) :=
    hAut.orderOf_coprime hodd.coprime_two_left _
  have hone : orderOf (phiAuto hP hXP ⟨h, hh⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdvd
  have hphi1 : phiAuto hP hXP ⟨h, hh⟩ = 1 := orderOf_eq_one_iff.mp hone
  let p' : ↥P := ⟨p, hp⟩
  have hsp : sylowPart hP hXP ⟨h, hh⟩ p' = p := by
    have hval : ((phiAuto hP hXP ⟨h, hh⟩ p' : ↥P) : G) = (p' : G) := by
      rw [hphi1]
      rfl
    rw [← phiAuto_apply hP hXP ⟨h, hh⟩ p']
    exact hval
  have hspec := oddPart_mul_sylowPart hP hXP ⟨h, hh⟩ p'
  rw [hsp] at hspec
  have hmain : h * p * h⁻¹ * p⁻¹ = oddPart hP hXP ⟨h, hh⟩ p' := by
    rw [show h * p * h⁻¹ = oddPart hP hXP ⟨h, hh⟩ p' * p from hspec.symm]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [hmain]
  exact oddPart_mem hP hXP ⟨h, hh⟩ p'

theorem sec11KB_hOdd [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P = X) (hAut : IsPGroup 2 (MulAut ↥P)) {h : G}
    (hh : h ∈ normalizer (X : Set G)) (hodd : Odd (orderOf h)) :
    ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ oddCoreIn X := by
  intro x hx
  obtain ⟨o, ho, p, hp, rfl⟩ := sylow_mul_oddCore hP hXP x hx
  have hho : h * o * h⁻¹ ∈ oddCoreIn X := sec11KB_conj_oddCore hh ho
  have hhp : h * p * h⁻¹ * p⁻¹ ∈ oddCoreIn X :=
    conj_mem_oddCore_of_sylow hP hXP hAut hh hodd hp
  have hdecomp : h * (o * p) * h⁻¹ * (o * p)⁻¹ =
      (h * o * h⁻¹) * (h * p * h⁻¹ * p⁻¹) * o⁻¹ := by group
  rw [hdecomp]
  exact mul_mem (mul_mem hho hhp) (inv_mem ho)

end CFSG.OddStandard.SmallF3.Omega
