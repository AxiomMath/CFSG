module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93R3SL23
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGLType
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93W

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section TwoLift

variable {Y' Y : Type} [Group Y'] [Finite Y'] [Group Y] [Finite Y]

theorem exists_two_lift (ρ : Y' →* Y) (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y)) {N : Subgroup Y'}
    {Qb : Subgroup Y} (hQb : IsPGroup 2 ↥Qb) (hle : Qb ≤ N.map ρ) :
    ∃ Q : Subgroup Y', Q ≤ N ∧ IsPGroup 2 ↥Q ∧ Q.map ρ = Qb ∧ ∀ a ∈ Q, ρ a = 1 → a = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' : Subgroup Y' := N ⊓ Qb.comap ρ with hN'
  let f : ↥N' →* Y := ρ.comp N'.subtype
  have hfr : f.range = Qb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := hle hy
      exact ⟨u, ⟨hu, hy⟩, rfl⟩
  have hkerodd : Odd (Nat.card f.ker) := by
    refine odd_card_of_forall_odd f.ker fun y hy => ?_
    have h1 : ((y : ↥N') : Y') ∈ ρ.ker := hy
    have := hodd _ h1
    rwa [Subgroup.orderOf_coe] at this
  have hcop : (Nat.card f.ker).Coprime f.ker.index := by
    rw [Subgroup.index_ker, hfr]
    obtain ⟨n, hn⟩ := hQb.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hkerodd)
  obtain ⟨H₁, hH₁⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hdisj : Disjoint f.ker H₁ := hH₁.disjoint
  have hsup : f.ker ⊔ H₁ = ⊤ := hH₁.sup_eq_top
  have hinj : ∀ h ∈ H₁, f h = 1 → h = 1 := by
    intro h hh hf
    have : h ∈ f.ker ⊓ H₁ := ⟨hf, hh⟩
    rw [hdisj.eq_bot] at this
    exact this
  refine ⟨H₁.map N'.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨h, -, rfl⟩
    exact h.2.1
  · intro g
    obtain ⟨h, hh, hg⟩ := g.2
    have hfh : f h ∈ Qb := by
      rw [← hfr]
      exact ⟨h, rfl⟩
    obtain ⟨k, hk⟩ := hQb ⟨f h, hfh⟩
    refine ⟨k, ?_⟩
    have h1 : f (h ^ 2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa [map_pow] using this
    have h2 : h ^ 2 ^ k = 1 := hinj _ (H₁.pow_mem hh _) h1
    apply Subtype.ext
    show (g : Y') ^ 2 ^ k = 1
    rw [← hg]
    have := congrArg Subtype.val h2
    simpa using this
  · rw [Subgroup.map_map]
    show H₁.map f = Qb
    have h1 : (⊤ : Subgroup ↥N').map f = f.range := (MonoidHom.range_eq_map f).symm
    rw [← hsup, Subgroup.map_sup, Subgroup.map_ker_self, bot_sup_eq, hfr] at h1
    exact h1
  · rintro _ ⟨h, hh, rfl⟩ ha
    have : h = 1 := hinj h hh ha
    rw [this, map_one]

end TwoLift

section OutLemma

variable {X : Type} [Group X] [Finite X]

theorem le_J_of_commutator (J : Subgroup X) [J.Normal] (hCJ : centralizer (J : Set X) ≤ J)
    (hOut : Odd (Nat.card ↥(commutator (Outer ↥J)))) {Q : Subgroup X} (hQ : IsPGroup 2 ↥Q)
    (hQX : Q ≤ commutator X) : Q ≤ J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : X →* Outer ↥J := (QuotientGroup.mk' (inner ↥J)).comp (MulAut.conjNormal (H := J))
  have hψ : ∀ q ∈ commutator X, ψ q ∈ commutator (Outer ↥J) := by
    intro q hq
    have h1 : q ∈ (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) := hq
    have h2 := Subgroup.mem_map_of_mem ψ h1
    rw [Subgroup.map_commutator] at h2
    exact Subgroup.commutator_mono le_top le_top h2
  intro q hqQ
  obtain ⟨k, hk⟩ := hQ ⟨q, hqQ⟩
  have hqk : q ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h3 : orderOf (ψ q) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hqk, map_one])
  have h4 : orderOf (ψ q) ∣ Nat.card ↥(commutator (Outer ↥J)) := by
    have := orderOf_dvd_natCard (⟨ψ q, hψ q (hQX hqQ)⟩ : ↥(commutator (Outer ↥J)))
    rwa [Subgroup.orderOf_mk] at this
  have h5 : orderOf (ψ q) = 1 := by
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(commutator (Outer ↥J))) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hOut)
    have := Nat.dvd_gcd h3 h4
    rw [hcop] at this
    exact Nat.dvd_one.1 this
  have hψq : ψ q = 1 := orderOf_eq_one_iff.1 h5
  have hmem : MulAut.conjNormal (H := J) q ∈ inner ↥J := (QuotientGroup.eq_one_iff _).1 hψq
  obtain ⟨j, hj⟩ := hmem
  have hc : (j : X)⁻¹ * q ∈ centralizer (J : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut ↥J => ((φ ⟨y, hy⟩ : ↥J) : X)) hj
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at h1
    have h1' : (j : X) * y * (j : X)⁻¹ = q * y * q⁻¹ := by simpa using h1
    calc y * ((j : X)⁻¹ * q) = (j : X)⁻¹ * ((j : X) * y * (j : X)⁻¹) * q := by group
      _ = (j : X)⁻¹ * (q * y * q⁻¹) * q := by rw [h1']
      _ = ((j : X)⁻¹ * q) * y := by group
  have : q = (j : X) * ((j : X)⁻¹ * q) := by group
  rw [this]
  exact J.mul_mem j.2 (hCJ hc)

end OutLemma

section Quat

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_quatW {H : Subgroup G} (hCH : Cen z ≤ H) (hz2 : orderOf z = 2)
    {r₁ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hsl₂ : HasSL2Model ↥L₂ (fun r => r = 3))
    (hzL₂ : toBar z ⟨z, mem_Cen_self z⟩ ∈ L₂)
    (hzJ : mkH H ⟨z, hCH (mem_Cen_self z)⟩ ∈ generalizedFitting (HBar H))
    {B : Subgroup (HBar H)} (hBC : B ≤ barIn H (Cen z))
    (hBmap : (B.subgroupOf (barIn H (Cen z))).map (cenToBar H hCH) = L₁)
    (hW : Ivk93W (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) r₁
      (B.subgroupOf (generalizedFitting (HBar H))))
    (hOut : Odd (Nat.card ↥(commutator (Outer ↥(generalizedFitting (HBar H)))))) :
    Ivk93WQuat (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H)))
      (B.subgroupOf (generalizedFitting (HBar H))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  set x : HBar H := mkH H ⟨z, hzmem⟩ with hx
  set C' : Subgroup (HBar H) := barIn H (Cen z) with hC'
  set J : Subgroup (HBar H) := generalizedFitting (HBar H) with hJ
  have : J.Normal := LocalCores.generalized_fitting_characteristic.2
  have hx2 : orderOf x = 2 := orderOf_mk_eq_two H (by rw [← Subgroup.orderOf_coe]; exact hz2)
  have hcent : centralizer ({x} : Set (HBar H)) = C' := centralizer_mk_eq H hz2 hzmem
  have hxC' : x ∈ C' := by
    rw [← hcent]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hcJ := centralizer_singleton_subgroupOf (J := J) hzJ
  rw [hcent] at hcJ
  let π := cenToBar H hCH
  let x₀ : ↥C' := ⟨x, hxC'⟩
  have hρx : π x₀ = toBar z ⟨z, mem_Cen_self z⟩ := cenToBar_cenMk H hCH ⟨z, mem_Cen_self z⟩
  have hodd : ∀ y ∈ π.ker, Odd (orderOf y) := fun y hy => odd_orderOf_of_cenToBar_eq_one H hCH y hy
  have hρ : Function.Surjective π := cenToBar_surjective H hCH
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hzb2 : toBar z ⟨z, mem_Cen_self z⟩ * toBar z ⟨z, mem_Cen_self z⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) * ⟨z, mem_Cen_self z⟩ = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hx₀2 : x₀ * x₀ = 1 := by
    apply Subtype.ext
    show x * x = 1
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  have hzb1 : toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := by
    intro h1
    have hk : x₀ ∈ π.ker := by rw [MonoidHom.mem_ker, hρx, h1]
    have h2 := hodd x₀ hk
    have : orderOf x₀ = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hx2
    rw [this] at h2
    exact absurd h2 (by decide)
  have hzbc : ∀ g ∈ L₂, g * toBar z ⟨z, mem_Cen_self z⟩ = toBar z ⟨z, mem_Cen_self z⟩ * g :=
    fun g _ => (Subgroup.mem_center_iff.mp (toBar_z_mem_center z) g)
  obtain ⟨Qb, hQbL, hQbc, hQb8, hQb2, hzbQb, a₀, ha₀, b₀, hb₀, ha₀2, hb₀2, hab₀⟩ :=
    sl23_q8_facts hsl₂ hzL₂ hzb2 hzb1 hzbc
  set Λ : Subgroup ↥C' := L₂.comap π with hΛ
  have hΛmap : Λ.map π = L₂ := Subgroup.map_comap_eq_self_of_surjective hρ L₂
  have hΛ'map : (⁅Λ, Λ⁆).map π = ⁅L₂, L₂⁆ := by
    rw [Subgroup.map_commutator, hΛmap]
  obtain ⟨Q₁, hQ₁N, hQ₁2, hQ₁map, hQ₁inj⟩ := exists_two_lift π hodd (N := ⁅Λ, Λ⁆) hQb2
    (by rw [hΛ'map]; exact hQbc)
  have hQcomm : Q₁.map C'.subtype ≤ commutator (HBar H) := by
    have h1 : Q₁ ≤ (⁅(⊤ : Subgroup ↥C'), ⊤⁆) := hQ₁N.trans (Subgroup.commutator_mono le_top le_top)
    have h2 := Subgroup.map_mono (f := C'.subtype) h1
    rw [Subgroup.map_commutator] at h2
    exact h2.trans (Subgroup.commutator_mono le_top le_top)
  have hQ2 : IsPGroup 2 ↥(Q₁.map C'.subtype) :=
    hQ₁2.of_surjective (C'.subtype.subgroupMap Q₁) (C'.subtype.subgroupMap_surjective Q₁)
  have hQJ : Q₁.map C'.subtype ≤ J :=
    le_J_of_commutator J (CFSG.centralizer_generalizedFitting_le (HBar H)) hOut hQ2 hQcomm
  obtain ⟨u, huQ, hu⟩ : ∃ u ∈ Q₁, π u = toBar z ⟨z, mem_Cen_self z⟩ := by
    have : toBar z ⟨z, mem_Cen_self z⟩ ∈ Q₁.map π := by rw [hQ₁map]; exact hzbQb
    exact this
  have hu2 : u * u = 1 := by
    apply hQ₁inj _ (Q₁.mul_mem huQ huQ)
    rw [map_mul, hu, hzb2]
  have hx₀c : ∀ y : ↥C', y * x₀ = x₀ * y := by
    intro y
    apply Subtype.ext
    have hy : (y : HBar H) ∈ centralizer ({x} : Set (HBar H)) := by rw [hcent]; exact y.2
    exact Subgroup.mem_centralizer_singleton_iff.1 hy
  have hw : u * x₀ = 1 := by
    have hw1 : u * x₀ ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, hu, hρx, hzb2]
    have hw2 : (u * x₀) * (u * x₀) = 1 := by
      calc (u * x₀) * (u * x₀) = u * (x₀ * u) * x₀ := by group
        _ = u * (u * x₀) * x₀ := by rw [← hx₀c u]
        _ = (u * u) * (x₀ * x₀) := by group
        _ = 1 := by rw [hu2, hx₀2, mul_one]
    have hod := hodd _ hw1
    have hdv : orderOf (u * x₀) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
    have h1 : orderOf (u * x₀) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdv with h | h
      · exact h
      · rw [h] at hod
        exact absurd hod (by decide)
    exact orderOf_eq_one_iff.1 h1
  have hux : u = x₀ := by
    have h1 : u = x₀⁻¹ := eq_inv_of_mul_eq_one_left hw
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hx₀2
  have hx₀Q : x₀ ∈ Q₁ := hux ▸ huQ
  set Qs : Subgroup (HBar H) := Q₁.map C'.subtype with hQs
  have hxQs : x ∈ Qs := ⟨x₀, hx₀Q, rfl⟩
  have hQsC : Qs ≤ C' := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hinjQ : Q₁ ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha1, ha2⟩
    exact Subgroup.mem_bot.2 (hQ₁inj a ha1 ha2)
  obtain ⟨ta, htaQ, hta⟩ : ∃ a ∈ Q₁, π a = a₀ := by
    have : a₀ ∈ Q₁.map π := by rw [hQ₁map]; exact ha₀
    exact this
  obtain ⟨tb, htbQ, htb⟩ : ∃ b ∈ Q₁, π b = b₀ := by
    have : b₀ ∈ Q₁.map π := by rw [hQ₁map]; exact hb₀
    exact this
  have hsq : ∀ {t : ↥C'}, t ∈ Q₁ → π t * π t = toBar z ⟨z, mem_Cen_self z⟩ → t * t = x₀ := by
    intro t htQ hπt
    have h1 : (t * t) * x₀⁻¹ = 1 :=
      hQ₁inj _ (Q₁.mul_mem (Q₁.mul_mem htQ htQ) (Q₁.inv_mem hx₀Q))
        (by rw [map_mul, map_mul, map_inv, hπt, hρx, mul_inv_cancel])
    exact mul_inv_eq_one.1 h1
  have hta2 : ta * ta = x₀ := hsq htaQ (by rw [hta, ha₀2])
  have htb2 : tb * tb = x₀ := hsq htbQ (by rw [htb, hb₀2])
  refine ⟨Qs.subgroupOf J, ?_, Subgroup.mem_subgroupOf.2 hxQs, ?_,
    ⟨⟨(ta : HBar H), hQJ ⟨ta, htaQ, rfl⟩⟩, Subgroup.mem_subgroupOf.2 ⟨ta, htaQ, rfl⟩,
      ⟨(tb : HBar H), hQJ ⟨tb, htbQ, rfl⟩⟩, Subgroup.mem_subgroupOf.2 ⟨tb, htbQ, rfl⟩,
      ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    rw [hcJ]
    exact Subgroup.mem_subgroupOf.2 (hQsC (Subgroup.mem_subgroupOf.1 hy))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQJ).toEquiv,
      Subgroup.card_map_of_injective C'.subtype_injective]
    obtain ⟨e⟩ := ivk93l_equiv_map π hinjQ
    rw [Nat.card_congr e.toEquiv, hQ₁map, hQb8]
  · exact Subtype.ext (congrArg (fun t : ↥C' => (t : HBar H)) hta2)
  · exact Subtype.ext (congrArg (fun t : ↥C' => (t : HBar H)) htb2)
  · intro hc
    have h1 : ta * tb = tb * ta := Subtype.ext (congrArg (fun t : ↥J => (t : HBar H)) hc)
    apply hab₀
    rw [← hta, ← htb, ← map_mul, ← map_mul, h1]
  · intro a ha b hb
    obtain ⟨u', hu'Q, hu'⟩ : ∃ u' ∈ Q₁, ((u' : ↥C') : HBar H) = (a : HBar H) := ha
    have hbB : (b : HBar H) ∈ B := Subgroup.mem_subgroupOf.1 hb
    let b₀' : ↥C' := ⟨(b : HBar H), hBC hbB⟩
    have hb₁ : π b₀' ∈ L₁ := by
      rw [← hBmap]
      exact ⟨b₀', Subgroup.mem_subgroupOf.2 hbB, rfl⟩
    have hu₂ : π u' ∈ L₂ := by
      apply hQbL
      rw [← hQ₁map]
      exact ⟨u', hu'Q, rfl⟩
    have hcc : π ⁅u', b₀'⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ hb₁ _ hu₂).symm
    have haC : a ∈ centralizer ({(⟨x, hzJ⟩ : ↥J)} : Set ↥J) := by
      rw [hcJ]
      exact Subgroup.mem_subgroupOf.2 (hQsC ⟨u', hu'Q, hu'⟩)
    have hbC : b ∈ centralizer ({(⟨x, hzJ⟩ : ↥J)} : Set ↥J) := hW.le hb
    have hcB : ⁅a, b⁆ ∈ B.subgroupOf J := by
      have h1 := hW.normal_in.conj_mem ⟨b, hbC⟩ (Subgroup.mem_subgroupOf.2 hb) ⟨a, haC⟩
      have h2 : a * b * a⁻¹ ∈ B.subgroupOf J := Subgroup.mem_subgroupOf.1 h1
      have h3 : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      rw [h3]
      exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hb)
    let ι : ↥(B.subgroupOf J) →* ↥C' :=
      { toFun := fun y => ⟨((y : ↥J) : HBar H), hBC (Subgroup.mem_subgroupOf.1 y.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro y y' h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : ↥C' => (t : HBar H)) h
    let ψ : ↥(B.subgroupOf J) →* CentralizerBar z := π.comp ι
    have hψker : ψ.ker ≤ pPrimeCore 2 ↥(B.subgroupOf J) := by
      have hodd' : Odd (Nat.card ψ.ker) := by
        refine odd_card_of_forall_odd ψ.ker fun y hy => ?_
        have h1 : ι y ∈ π.ker := hy
        have := hodd _ h1
        rwa [orderOf_injective ι hι] at this
      exact GroupTheory.le_pPrimeCore_of_normal ψ.normal_ker (Nat.coprime_two_left.2 hodd')
    have hψc : (⟨⁅a, b⁆, hcB⟩ : ↥(B.subgroupOf J)) ∈ ψ.ker := by
      have h1 : ι ⟨⁅a, b⁆, hcB⟩ = ⁅u', b₀'⁆ := by
        apply Subtype.ext
        show (((⁅a, b⁆ : ↥J)) : HBar H) = (((⁅u', b₀'⁆ : ↥C')) : HBar H)
        have e1 : (((⁅a, b⁆ : ↥J)) : HBar H) = ⁅(a : HBar H), (b : HBar H)⁆ := by
          simp [commutatorElement_def]
        have e2 : (((⁅u', b₀'⁆ : ↥C')) : HBar H) = ⁅((u' : ↥C') : HBar H), (b : HBar H)⁆ := by
          simp [commutatorElement_def, b₀']
        rw [e1, e2, hu']
      rw [MonoidHom.mem_ker]
      show π (ι ⟨⁅a, b⁆, hcB⟩) = 1
      rw [h1]
      exact hcc
    exact ⟨⟨⁅a, b⁆, hcB⟩, hψker hψc, rfl⟩

end Quat

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
