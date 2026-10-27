module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Swap
public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Final
public import CFSG.CGT.PushingUpLit.LIT.Foote.L56EG

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3
  (Theorem3Statement Frame SylowFrame exists_isSylowOf_le rightConjugate_le_rightConjugate
    exists_rightConjugate_le_of_isSylowOf conj_mem_rightConjugate)

variable {G : Type} [Group G] [Finite G]

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem false_of_swap (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) (hTwo : TwoOrbit M J)
    {g : G} {T S : Subgroup G} (hgood : Good56 M J g)
    (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2)
    (hS : SylowFrame J T S) (hncent : ¬ ∀ t ∈ T, ∀ v ∈ blockU J, t * v = v * t)
    {x : G} (hxJ : x ∈ J) (hxM : x ∈ rightConjugate M g)
    (hxB : x ∉ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G))
    (hxW : rightConjugate T x ≤ S ⊓ Subgroup.normalizer (T : Set G))
    {y : G} (hyJ : y ∈ J)
    (hyN : rightConjugate (S ⊓ Subgroup.normalizer (T : Set G)) y ≤
      S ⊓ Subgroup.normalizer ((S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G))
    (hnT : ¬ rightConjugate T y ≤ S ⊓ Subgroup.normalizer (T : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := c.block
  have hg : g ∉ M := hgood.1
  obtain ⟨hTc, hTs, hQV, hQT⟩ := c.partC hA hz hgood hT hmax hS hncent
  have hT1 : T ≠ ⊥ := sylow_ne_bot56 hgood hT
  have hTB : T ≤ rightConjugate J g := hT.le.trans inf_le_left
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hS.le_normalizer
  have hTJ : T ⊓ J = ⊥ := hS.inf_eq_bot
  have hTW : T ≤ S ⊓ Subgroup.normalizer (T : Set G) := le_inf hS.le Subgroup.le_normalizer
  have h4T : 4 ≤ Nat.card T := by
    obtain ⟨W₀, hWle, hW2, hW4⟩ := hgood.2
    have hWp : IsPGroup 2 W₀ := IsPGroup.of_card (n := 2) (by rw [hW4]; norm_num)
    have := card_le_of_isSylowOf hT hWle hWp
    omega
  have hTyN : ∀ u ∈ rightConjugate T y, u ∈ S ∧ u ∈ Subgroup.normalizer
      ((S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) := fun u hu =>
    hyN ((rightConjugate_le_rightConjugate hTW y) hu)
  have hTys : ∀ u ∈ rightConjugate T y, u * u = 1 := by
    intro u hu
    have h1 := hTs _ ((mem_rightConjugate_iff T y u).1 hu)
    have e : u * u = y⁻¹ * ((y * u * y⁻¹) * (y * u * y⁻¹)) * y := by group
    rw [e, h1]
    group
  have hTyc : ∀ s ∈ rightConjugate T y, ∀ s' ∈ rightConjugate T y, s * s' = s' * s := by
    intro s hs s' hs'
    have h1 := hTc _ ((mem_rightConjugate_iff T y s).1 hs) _ ((mem_rightConjugate_iff T y s').1 hs')
    have e1 : s * s' = y⁻¹ * ((y * s * y⁻¹) * (y * s' * y⁻¹)) * y := by group
    have e2 : s' * s = y⁻¹ * ((y * s' * y⁻¹) * (y * s * y⁻¹)) * y := by group
    rw [e1, e2, h1]
  suffices key : ∃ u ∈ rightConjugate T y, u ∉ S ⊓ Subgroup.normalizer (T : Set G) ∧
      u ∈ rightConjugate M g by
    obtain ⟨u, huT, huW, huM⟩ := key
    exact c.false_of_mem_conj hA hz hTwo hgood hT hmax hS hncent hyJ hyN huT huW huM
  have hCt : ∀ t ∈ T, t ≠ 1 → Subgroup.centralizer ({t} : Set G) ≤ rightConjugate M g := by
    intro t ht ht1
    exact c.centralizer_le_conj (hTB ht) ⟨1, by rw [pow_one, pow_two]; exact hTs t ht⟩ ht1
  by_cases hcase : ∃ u ∈ rightConjugate T y, u ∉ S ⊓ Subgroup.normalizer (T : Set G) ∧
      ∃ t ∈ T, t ≠ 1 ∧ u * t = t * u
  · obtain ⟨u, huT, huW, t, ht, ht1, hut⟩ := hcase
    exact ⟨u, huT, huW, hCt t ht ht1 (Subgroup.mem_centralizer_singleton_iff.2 hut)⟩
  push Not at hcase
  by_cases hR : ∃ u₀ ∈ rightConjugate T y, u₀ ∈ S ⊓ Subgroup.normalizer (T : Set G) ∧ u₀ ≠ 1
  ·
    obtain ⟨u₀, hu₀T, hu₀W, hu₀1⟩ := hR
    obtain ⟨u, huT, huW⟩ := IsConcreteLE.not_le_iff_exists.1 hnT
    refine ⟨u, huT, huW, ?_⟩
    obtain ⟨t, ht, q, hq, hu₀eq⟩ := X_decomp hS hu₀W
    have hqJ : q ∈ J := (Subgroup.mem_inf.1 hq).2
    have ht1 : t ≠ 1 := by
      rintro rfl
      apply hu₀1
      have h1 : u₀ ∈ rightConjugate T y ⊓ J := ⟨hu₀T, by rw [hu₀eq, one_mul]; exact hqJ⟩
      rw [rightConjugate_inf_eq_bot hTJ hyJ, Subgroup.mem_bot] at h1
      exact h1
    have hgy : g * y ∉ M := fun h => hg (by
      have := M.mul_mem h (M.inv_mem (c.le hyJ))
      simpa using this)
    have hu₀J₃ : u₀ ∈ rightConjugate J (g * y) := by
      have := (rightConjugate_le_rightConjugate hTB y) hu₀T
      rwa [rightConjugate_mul] at this
    have hCu₀ := c.centralizer_le_conj hu₀J₃ ⟨1, by rw [pow_one, pow_two]; exact hTys u₀ hu₀T⟩ hu₀1
    have hQcomm : ∀ q' ∈ S ⊓ Subgroup.normalizer (T : Set G) ⊓ J, q' * u₀ = u₀ * q' := by
      intro q' hq'
      have hq'T := inf_comm_T hS q' hq'
      calc q' * u₀ = q' * (t * q) := by rw [hu₀eq]
        _ = (q' * t) * q := by group
        _ = (t * q') * q := by rw [hq'T t ht]
        _ = t * (q' * q) := by group
        _ = t * (q * q') := by rw [hJ.blockU_comm q' (hQV hq') q (hQV hq)]
        _ = (t * q) * q' := by group
        _ = u₀ * q' := by rw [hu₀eq]
    have hQM : S ⊓ Subgroup.normalizer (T : Set G) ⊓ J ≤ rightConjugate M (g * y) := fun q' hq' =>
      hCu₀ (Subgroup.mem_centralizer_singleton_iff.2 (hQcomm q' hq'))
    have hQN : S ⊓ Subgroup.normalizer (T : Set G) ⊓ J ≤
        Subgroup.normalizer ((rightConjugate J (g * y) : Subgroup G) : Set G) :=
      c.le_normalizer_of_le_M hA hz hgy (fun a ha a' ha' => hJ.blockU_comm a (hQV ha) a' (hQV ha'))
        (fun a ha => hJ.blockU_sq_eq_one a (hQV ha)) (by rw [hQT]; exact h4T) inf_le_right hQM
    have hQs : ∀ q' ∈ S ⊓ Subgroup.normalizer (T : Set G) ⊓ J, ∀ s ∈ rightConjugate T y,
        q' * s = s * q' := by
      intro q' hq' s hs
      have hsS := (hTyN s hs).1
      have hsJ₃ : s ∈ rightConjugate J (g * y) := by
        have := (rightConjugate_le_rightConjugate hTB y) hs
        rwa [rightConjugate_mul] at this
      have hsNJ : s ∈ Subgroup.normalizer (J : Set G) :=
        (sup_le Subgroup.le_normalizer hTN : J ⊔ T ≤ Subgroup.normalizer (J : Set G))
          (hS.sylow.le hsS)
      have hq'J : q' ∈ J := (Subgroup.mem_inf.1 hq').2
      have hq'S : q' ∈ S := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hq').1).1
      have hc₀J₃ : q' * s * q'⁻¹ * s⁻¹ ∈ rightConjugate J (g * y) :=
        (rightConjugate J (g * y)).mul_mem
          ((Subgroup.mem_normalizer_iff.1 (hQN hq') s).1 hsJ₃)
          ((rightConjugate J (g * y)).inv_mem hsJ₃)
      have hc₀J : q' * s * q'⁻¹ * s⁻¹ ∈ J := by
        have h1 := (Subgroup.mem_normalizer_iff.1 hsNJ q'⁻¹).1 (J.inv_mem hq'J)
        have e : q' * s * q'⁻¹ * s⁻¹ = q' * (s * q'⁻¹ * s⁻¹) := by group
        rw [e]
        exact J.mul_mem hq'J h1
      have hc₀S : q' * s * q'⁻¹ * s⁻¹ ∈ S :=
        S.mul_mem (S.mul_mem (S.mul_mem hq'S hsS) (S.inv_mem hq'S)) (S.inv_mem hsS)
      have h2 : ∃ n : ℕ, (q' * s * q'⁻¹ * s⁻¹) ^ 2 ^ n = 1 := by
        obtain ⟨n, hn⟩ := hS.sylow.isPGroup ⟨_, hc₀S⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
      have h3 := c.eq_one_of_mem_inf hgy hc₀J hc₀J₃ h2
      calc q' * s = (q' * s * q'⁻¹ * s⁻¹) * (s * q') := by group
        _ = s * q' := by rw [h3, one_mul]
    have hsq := hQs q hq u huT
    have hsu : u * u₀ = u₀ * u := hTyc u huT u₀ hu₀T
    have hut : u * t = t * u := by
      have ht_eq : t = u₀ * q⁻¹ := by rw [hu₀eq]; group
      have hsq' : u * q⁻¹ = q⁻¹ * u := by
        calc u * q⁻¹ = q⁻¹ * (q * u) * q⁻¹ := by group
          _ = q⁻¹ * (u * q) * q⁻¹ := by rw [hsq]
          _ = q⁻¹ * u := by group
      calc u * t = u * (u₀ * q⁻¹) := by rw [← ht_eq]
        _ = (u * u₀) * q⁻¹ := by group
        _ = (u₀ * u) * q⁻¹ := by rw [hsu]
        _ = u₀ * (u * q⁻¹) := by group
        _ = u₀ * (q⁻¹ * u) := by rw [hsq']
        _ = (u₀ * q⁻¹) * u := by group
        _ = t * u := by rw [← ht_eq]
    exact hCt t ht ht1 (Subgroup.mem_centralizer_singleton_iff.2 hut)
  push Not at hR
  have hc₁ := c.transport g
  have hne : rightConjugate (rightConjugate J g) x ≠ rightConjugate J g := fun h =>
    hxB ((rightConjugate_eq_self_iff _ x).1 h)
  have hBB : ∀ b ∈ rightConjugate J g, ∀ b' ∈ rightConjugate (rightConjugate J g) x,
      b * b' = b' * b := by
    intro b hb b' hb'
    have hcomm := hc₁.commutator_conj_eq_bot hxM hne
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hb
    exact (Subgroup.mem_centralizer_iff.1 this b' hb').symm
  have hβ : ∀ t ∈ T, t * (x⁻¹ * t * x) ∈ S ⊓ Subgroup.normalizer (T : Set G) ⊓ J := by
    intro t ht
    have h1 : x⁻¹ * t * x ∈ S ⊓ Subgroup.normalizer (T : Set G) :=
      hxW ((mem_rightConjugate_iff T x _).2 (by
        have e : x * (x⁻¹ * t * x) * x⁻¹ = t := by group
        rw [e]
        exact ht))
    refine ⟨(S ⊓ Subgroup.normalizer (T : Set G)).mul_mem (hTW ht) h1, ?_⟩
    have e : t * (x⁻¹ * t * x) = (t * x⁻¹ * t⁻¹) * (t * t) * x := by group
    rw [e, hTs t ht, mul_one]
    exact J.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTN ht) x⁻¹).1 (J.inv_mem hxJ)) hxJ
  obtain ⟨t₁, ht₁, hβ1⟩ : ∃ t ∈ T, t * (x⁻¹ * t * x) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht, k, hk, htk⟩ := c.exists_noncentral hA hz hg hT hT1
    apply htk
    have hxt : x⁻¹ * t * x = t := by
      have h1 := hcon t ht
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hTs t ht)
      have h2 : x⁻¹ * t * x = t⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2, hti]
    have htx : t * x = x * t := by
      calc t * x = x * (x⁻¹ * t * x) := by group
        _ = x * t := by rw [hxt]
    have htB' : t ∈ rightConjugate (rightConjugate J g) x := by
      rw [mem_rightConjugate_iff]
      have e : x * t * x⁻¹ = t := by
        calc x * t * x⁻¹ = (t * x) * x⁻¹ := by rw [htx]
          _ = t := by group
      rw [e]
      exact hTB ht
    exact (hBB k hk t htB').symm
  have ht₁1 : t₁ ≠ 1 := fun h => hβ1 (by rw [h]; group)
  have hψ : ∀ u ∈ rightConjugate T y,
      t₁ * (u⁻¹ * t₁ * u) ∈ S ⊓ Subgroup.normalizer (T : Set G) ⊓ J := by
    intro u hu
    obtain ⟨huS, huNW⟩ := hTyN u hu
    have h1 : u⁻¹ * t₁ * u ∈ S ⊓ Subgroup.normalizer (T : Set G) := by
      refine (Subgroup.mem_normalizer_iff.1 huNW (u⁻¹ * t₁ * u)).2 ?_
      have e : u * (u⁻¹ * t₁ * u) * u⁻¹ = t₁ := by group
      rw [e]
      exact hTW ht₁
    exact ⟨(S ⊓ Subgroup.normalizer (T : Set G)).mul_mem (hTW ht₁) h1,
      mul_conj_mem_of_mem_S hS hTc hTs huS ht₁⟩
  let ψ : ↥(rightConjugate T y) → ↥(S ⊓ Subgroup.normalizer (T : Set G) ⊓ J) := fun u =>
    ⟨t₁ * ((u : G)⁻¹ * t₁ * u), hψ u u.2⟩
  have hinj : Function.Injective ψ := by
    intro u u' h
    have h1 : t₁ * ((u : G)⁻¹ * t₁ * u) = t₁ * ((u' : G)⁻¹ * t₁ * u') := congrArg Subtype.val h
    have h2 : (u : G)⁻¹ * t₁ * u = (u' : G)⁻¹ * t₁ * u' := mul_left_cancel h1
    have hw : (u' : G) * (u : G)⁻¹ ∈ rightConjugate T y :=
      (rightConjugate T y).mul_mem u'.2 ((rightConjugate T y).inv_mem u.2)
    have hwt : (u' : G) * (u : G)⁻¹ * t₁ = t₁ * ((u' : G) * (u : G)⁻¹) := by
      calc (u' : G) * (u : G)⁻¹ * t₁ = u' * ((u : G)⁻¹ * t₁ * u) * (u : G)⁻¹ := by group
        _ = u' * ((u' : G)⁻¹ * t₁ * u') * (u : G)⁻¹ := by rw [h2]
        _ = t₁ * ((u' : G) * (u : G)⁻¹) := by group
    have hwW : (u' : G) * (u : G)⁻¹ ∈ S ⊓ Subgroup.normalizer (T : Set G) := by
      by_contra hwW'
      exact hcase _ hw hwW' t₁ ht₁ ht₁1 hwt
    have hw1 : (u' : G) * (u : G)⁻¹ = 1 := hR _ hw hwW
    exact Subtype.ext (mul_inv_eq_one.1 hw1).symm
  have hbij : Function.Bijective ψ :=
    hinj.bijective_of_nat_card_le (by rw [rightConjugate_card]; exact le_of_eq hQT)
  obtain ⟨u, hu⟩ := hbij.2 ⟨t₁ * (x⁻¹ * t₁ * x), hβ t₁ ht₁⟩
  have h1 : t₁ * ((u : G)⁻¹ * t₁ * u) = t₁ * (x⁻¹ * t₁ * x) := congrArg Subtype.val hu
  have h2 : (u : G)⁻¹ * t₁ * u = x⁻¹ * t₁ * x := mul_left_cancel h1
  have hxu : x * (u : G)⁻¹ * t₁ = t₁ * (x * (u : G)⁻¹) := by
    calc x * (u : G)⁻¹ * t₁ = x * ((u : G)⁻¹ * t₁ * u) * (u : G)⁻¹ := by group
      _ = x * (x⁻¹ * t₁ * x) * (u : G)⁻¹ := by rw [h2]
      _ = t₁ * (x * (u : G)⁻¹) := by group
  have hxuM : x * (u : G)⁻¹ ∈ rightConjugate M g :=
    hCt t₁ ht₁ ht₁1 (Subgroup.mem_centralizer_singleton_iff.2 hxu)
  have huM : (u : G) ∈ rightConjugate M g := by
    have h3 := (rightConjugate M g).mul_mem ((rightConjugate M g).inv_mem hxM) hxuM
    have e : x⁻¹ * (x * (u : G)⁻¹) = (u : G)⁻¹ := by group
    rw [e] at h3
    simpa using (rightConjugate M g).inv_mem h3
  have huW : (u : G) ∉ S ⊓ Subgroup.normalizer (T : Set G) := by
    intro huW
    have hu1 : (u : G) = 1 := hR _ u.2 huW
    apply hβ1
    rw [hu1] at h2
    have h3 : x⁻¹ * t₁ * x = t₁ := by simpa using h2.symm
    rw [h3]
    exact hTs t₁ ht₁
  exact ⟨u, u.2, huW, huM⟩

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
