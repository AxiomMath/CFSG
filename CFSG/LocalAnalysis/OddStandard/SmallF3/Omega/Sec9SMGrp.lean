module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem card_orbit_mul_card_stabilizer_eq {G B : Type*} [Group G] [MulAction G B]
    (b : B) :
    Nat.card (MulAction.orbit G b) * Nat.card (MulAction.stabilizer G b) = Nat.card G := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G b)
  rwa [Nat.card_prod] at h

theorem sec9m_exists_twoPart {X Y : Type*} [Group X] [Finite X] [Group Y] (f : X →* Y) (x : X)
    {m : ℕ} (hm : f x ^ (2 ^ m) = 1) : ∃ y : X, (∃ j : ℕ, y ^ (2 ^ j) = 1) ∧ f y = f x := by
  obtain ⟨a, u, hu, hau⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hcop : u.Coprime (orderOf (f x)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hm)
      (Nat.Coprime.pow_right m (Odd.coprime_two_right hu))
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨x ^ (u * k), ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, show u * k * 2 ^ a = orderOf x * k by rw [hau]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, pow_mul, hk]

theorem sec9m_card_mulAut {G : Type} [Group G] [Finite G] {B : Subgroup G}
    (hB : IsElemAb2 B 4) : Nat.card (MulAut ↥B) = 20160 := by
  have hcomm : ∀ a b : ↥B, a * b = b * a := fun a b => hB.1.1.is_comm.comm a b
  have hpow : ∀ a : ↥B, a ^ 2 = 1 := by
    intro a
    apply Subtype.ext
    simpa using hB.1.2 (a : G) a.2
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := ↥B)
    hcomm hpow (n := 4) hB.2
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod 4]
  decide

theorem sec9m_card_mul_dvd {Γ : Type*} [Group Γ] [Finite Γ] {H K R : Subgroup Γ}
    (hKH : K ≤ H) (hRH : R ≤ H) (hnorm : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (hinf : K ⊓ R = ⊥) : Nat.card K * Nat.card R ∣ Nat.card H := by
  have hnormN : K ≤ Subgroup.normalizer (R : Set Γ) :=
    Subgroup.le_normalizer_iff.mpr (fun k hk r hr => hnorm k (hKH hk) r hr)
  have hdisj : Disjoint R K := by
    rw [disjoint_iff, inf_comm]
    exact hinf
  have hcard :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R K hnormN hdisj
  have hdvd : Nat.card (R ⊔ K : Subgroup Γ) ∣ Nat.card H :=
    Subgroup.card_dvd_of_le (sup_le hRH hKH)
  rw [hcard, mul_comm (Nat.card R) (Nat.card K)] at hdvd
  exact hdvd

private def neOneMulAction {B : Type*} [Group B] (H : Subgroup (MulAut B)) :
    MulAction ↥H {b : B // b ≠ 1} where
  smul h x := ⟨h.1 x.1, fun hx => x.2 (h.1.injective (by rw [hx, map_one]))⟩
  one_smul x := Subtype.ext rfl
  mul_smul h₁ h₂ x := Subtype.ext rfl

theorem sec9m_normal_fixes {B : Type*} [Group B] [Finite B] {H R : Subgroup (MulAut B)}
    (hRH : R ≤ H) (hnorm : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (htrans : ∀ b b' : B, b ≠ 1 → b' ≠ 1 → ∃ h ∈ H, h b = b')
    (hcop : Nat.Coprime (Nat.card R) (Nat.card B - 1)) :
    ∀ r ∈ R, ∀ b : B, r b = b := by
  classical
  intro r hr b
  by_cases hb : b = 1
  · subst hb
    exact map_one r
  · let s := {b : B // b ≠ 1}
    letI : MulAction ↥H s := neOneMulAction H
    haveI hpre : MulAction.IsPretransitive ↥H s :=
      ⟨fun x y => by
        obtain ⟨h, hh, hhx⟩ := htrans x.1 y.1 x.2 y.2
        exact ⟨⟨h, hh⟩, Subtype.ext hhx⟩⟩
    have hHnorm : H ≤ Subgroup.normalizer (R : Set (MulAut B)) :=
      Subgroup.le_normalizer_iff.mpr hnorm
    haveI hN : (R.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHnorm
    let a : s := ⟨b, hb⟩
    have hblock : MulAction.IsBlock ↥H (MulAction.orbit (R.subgroupOf H) a) :=
      MulAction.IsBlock.orbit_of_normal a
    have hdvd_s : Nat.card (MulAction.orbit (R.subgroupOf H) a) ∣ Nat.card s :=
      MulAction.IsBlock.ncard_dvd_card hblock ⟨a, MulAction.mem_orbit_self a⟩
    have hcard_N : Nat.card (R.subgroupOf H) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
    have hdvd_R : Nat.card (MulAction.orbit (R.subgroupOf H) a) ∣ Nat.card R := by
      have h := card_orbit_mul_card_stabilizer_eq (G := ↥(R.subgroupOf H)) a
      rw [hcard_N] at h
      exact ⟨_, h.symm⟩
    have hcop_s : Nat.Coprime (Nat.card R) (Nat.card s) := by
      have hs : Nat.card s + 1 = Nat.card B := by
        have h := Nat.card_congr (Equiv.optionSubtypeNe (1 : B))
        rwa [Finite.card_option] at h
      have hB1 : Nat.card B - 1 = Nat.card s := by omega
      rwa [hB1] at hcop
    have hd1 : Nat.card (MulAction.orbit (R.subgroupOf H) a) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop_s hdvd_R hdvd_s
    haveI : Subsingleton (MulAction.orbit (R.subgroupOf H) a) :=
      Finite.card_le_one_iff_subsingleton.mp (le_of_eq hd1)
    have htriv : ∀ n : R.subgroupOf H, n • a = a := by
      intro n
      exact congrArg Subtype.val (Subsingleton.elim
        (⟨n • a, MulAction.mem_orbit a n⟩ : MulAction.orbit (R.subgroupOf H) a)
        ⟨a, MulAction.mem_orbit_self a⟩)
    have h2 : (⟨⟨r, hRH hr⟩, hr⟩ : R.subgroupOf H) • a = a := htriv _
    have h3 : ((⟨⟨r, hRH hr⟩, hr⟩ : R.subgroupOf H) : ↥H).1 b = b :=
      congrArg Subtype.val h2
    exact h3

theorem sec9m_card_range_le {E F Y : Type*} [Group E] [Group F] [Group Y] [Finite F]
    (ψ : E →* F) (hψ : Function.Surjective ψ) (c : E →* Y) (hker : ψ.ker ≤ c.ker) :
    Nat.card c.range ≤ Nat.card F := by
  have hF : Nat.card F = ψ.ker.index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top]
  have hdvd : c.ker.index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hker
  calc Nat.card c.range = c.ker.index := (Subgroup.index_ker c).symm
    _ ≤ ψ.ker.index := Nat.le_of_dvd (by rw [← hF]; exact Nat.card_pos) hdvd
    _ = Nat.card F := hF.symm

theorem sec9m_card_range_le_sup {G : Type*} [Group G] {M E O : Subgroup G} (hEM : E ≤ M)
    (hOM : O ≤ M) (hM : M ≤ E ⊔ O) {Y F : Type*} [Group Y] [Group F] [Finite F]
    (f : ↥M →* Y) (hO : ∀ o : ↥M, (o : G) ∈ O → f o = 1)
    (ψ : ↥E →* F) (hψ : Function.Surjective ψ)
    (hker : ∀ e : ↥E, ψ e = 1 → ∀ he : (e : G) ∈ M, f ⟨e, he⟩ = 1) :
    Nat.card f.range ≤ Nat.card F := by
  let c : ↥E →* Y := f.comp (Subgroup.inclusion hEM)
  have hc : Nat.card c.range ≤ Nat.card F := by
    apply sec9m_card_range_le ψ hψ c
    intro e he
    rw [MonoidHom.mem_ker] at he ⊢
    exact hker e he (hEM e.2)
  have hEc : E.subgroupOf M ≤ c.range.comap f := by
    intro e he
    rw [Subgroup.mem_comap]
    have hx : Subgroup.inclusion hEM ⟨(e : G), Subgroup.mem_subgroupOf.mp he⟩ = e :=
      Subtype.ext rfl
    refine MonoidHom.mem_range.mpr ⟨⟨(e : G), Subgroup.mem_subgroupOf.mp he⟩, ?_⟩
    show f ((Subgroup.inclusion hEM) ⟨(e : G), Subgroup.mem_subgroupOf.mp he⟩) = f e
    rw [hx]
  have hOc : O.subgroupOf M ≤ c.range.comap f := by
    intro o ho
    rw [Subgroup.mem_comap, hO o (Subgroup.mem_subgroupOf.mp ho)]
    exact c.range.one_mem
  have hsup : (E ⊔ O).subgroupOf M = E.subgroupOf M ⊔ O.subgroupOf M :=
    Subgroup.subgroupOf_sup hEM hOM
  have htop : c.range.comap f = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← Subgroup.subgroupOf_eq_top.mpr hM, hsup]
    exact sup_le hEc hOc
  have hfr : f.range ≤ c.range := by
    intro y hy
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hy
    have hm : m ∈ c.range.comap f := by rw [htop]; trivial
    rwa [Subgroup.mem_comap] at hm
  have hcr : c.range ≤ f.range := by
    rintro y ⟨e, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨Subgroup.inclusion hEM e, rfl⟩
  have hceq : c.range = f.range := le_antisymm hcr hfr
  rw [hceq] at hc
  exact hc

end CFSG.OddStandard.SmallF3.Omega
