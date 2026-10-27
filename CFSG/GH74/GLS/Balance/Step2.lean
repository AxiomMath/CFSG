module

public import CFSG.GH74.GLS.Balance.PStarUtil
public import CFSG.GH74.GLS.Balance.SolvAPIDefs
public import CFSG.GH74.GLS.TwoThin.Struct

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem exists_odd_subgroup_of_two_prime {x : X} {V : Subgroup X} (A : SolvAPI x V) {v : X}
    (hv : v ∈ V) (hv2 : Nat.Coprime (orderOf v) 2) :
    ∃ V₁ : Subgroup X, v ∈ V₁ ∧ V₁ ≤ V ∧ Odd (Nat.card V₁) ∧
      ∀ g ∈ V, (∀ v' ∈ V, ⁅g, v'⁆ ∈ pPrimeCoreOf 2 (centralizer ({x} : Set X))) →
        g ∈ normalizer (V₁ : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := centralizer ({x} : Set X) with hC
  have hVC : V ≤ C := A.hVC
  set Ō : Subgroup ↥C := pPrimeCore 2 ↥C with hŌ
  set mkO : ↥C →* ↥C ⧸ Ō := QuotientGroup.mk' Ō with hmkO
  let v' : ↥C := ⟨v, hVC hv⟩
  set V₁c : Subgroup ↥C := (zpowers (mkO v')).comap mkO with hV₁c
  have hŌodd : Odd (Nat.card Ō) := TwoThin.odd_card_pPrimeCore _
  have hmem : ∀ g : ↥C, g ∈ V₁c ↔ ∃ i : ℤ, mkO g = mkO v' ^ i := by
    intro g
    rw [hV₁c, Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  have hdecomp : ∀ g : ↥C, g ∈ V₁c → ∃ i : ℤ, ∃ o ∈ Ō, g = v' ^ i * o := by
    intro g hg
    obtain ⟨i, hi⟩ := (hmem g).mp hg
    refine ⟨i, (v' ^ i)⁻¹ * g, ?_, by group⟩
    have : mkO (v' ^ i) = mkO g := by rw [map_zpow]; exact hi.symm
    exact (QuotientGroup.eq).mp this
  refine ⟨V₁c.map C.subtype, ⟨v', ?_, rfl⟩, ?_, ?_, ?_⟩
  · exact (hmem v').mpr ⟨1, by simp⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, o, ho, rfl⟩ := hdecomp g hg
    have hoV : ((o : ↥C) : X) ∈ V := A.O_le_V ⟨o, ho, rfl⟩
    have hvi : (((v' ^ i : ↥C)) : X) ∈ V := by
      show (v' : X) ^ i ∈ V
      exact zpow_mem hv i
    simpa using mul_mem hvi hoV
  ·
    rw [Nat.card_congr (Subgroup.equivMapOfInjective V₁c C.subtype C.subtype_injective).toEquiv.symm]
    by_contra hnot
    have h2 : 2 ∣ Nat.card V₁c := by
      rcases Nat.even_or_odd (Nat.card V₁c) with h | h
      · exact even_iff_two_dvd.mp h
      · exact absurd h hnot
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := V₁c) 2 h2
    have hgC : orderOf (g : ↥C) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
    have hm : Odd (orderOf v') := by
      rw [show orderOf v' = orderOf v from Subgroup.orderOf_mk _ _]
      exact Nat.coprime_two_right.mp hv2
    obtain ⟨i, o, ho, hgi⟩ := hdecomp (g : ↥C) g.2
    have hpow : ((g : ↥C)) ^ orderOf v' ∈ Ō := by
      rw [← QuotientGroup.eq_one_iff]
      show mkO ((g : ↥C) ^ orderOf v') = 1
      rw [map_pow]
      obtain ⟨j, hj⟩ := (hmem (g : ↥C)).mp g.2
      rw [hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow,
        pow_orderOf_eq_one, map_one, one_zpow]
    have hodd1 : Odd (orderOf (⟨(g : ↥C) ^ orderOf v', hpow⟩ : Ō)) :=
      Odd.of_dvd_nat hŌodd (orderOf_dvd_natCard _)
    rw [Subgroup.orderOf_mk] at hodd1
    have hdvd : orderOf (g : ↥C) ∣ orderOf v' * orderOf ((g : ↥C) ^ orderOf v') := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, pow_orderOf_eq_one]
    have hodd2 : Odd (orderOf (g : ↥C)) := Odd.of_dvd_nat (hm.mul hodd1) hdvd
    rw [hgC] at hodd2
    exact absurd hodd2 (by decide)
  · intro g hgV hcomm
    have hgC : g ∈ C := hVC hgV
    let g' : ↥C := ⟨g, hgC⟩
    have hcomm1 : mkO g' * mkO v' = mkO v' * mkO g' := by
      obtain ⟨o, ho, hoe⟩ := hcomm v hv
      have h1 : o = g' * v' * g'⁻¹ * v'⁻¹ := by
        apply Subtype.ext
        have hoe' : (o : X) = ⁅g, v⁆ := hoe
        rw [hoe']
        simp [commutatorElement_def, g', v']
      have h2 : mkO o = 1 := (QuotientGroup.eq_one_iff _).mpr ho
      rw [h1] at h2
      simp only [map_mul, map_inv] at h2
      calc mkO g' * mkO v' = mkO g' * mkO v' * (mkO g')⁻¹ * (mkO v')⁻¹ * (mkO v' * mkO g') := by group
        _ = mkO v' * mkO g' := by rw [h2]; group
    have hcentr : ∀ z ∈ zpowers (mkO v'), mkO g' * z = z * mkO g' := by
      intro z hz
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact ((show Commute (mkO g') (mkO v') from hcomm1).zpow_right i).eq
    have hcentr' : ∀ z ∈ zpowers (mkO v'), (mkO g')⁻¹ * z * mkO g' = z := by
      intro z hz
      have := hcentr z hz
      calc (mkO g')⁻¹ * z * mkO g' = (mkO g')⁻¹ * (z * mkO g') := by group
        _ = (mkO g')⁻¹ * (mkO g' * z) := by rw [this]
        _ = z := by group
    have key : ∀ y_c : ↥C, y_c ∈ V₁c ↔ g' * y_c * g'⁻¹ ∈ V₁c := by
      intro y_c
      rw [hV₁c, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
      constructor
      · intro hy
        have e : mkO g' * mkO y_c * (mkO g')⁻¹ = mkO y_c := by rw [hcentr _ hy]; group
        rw [e]; exact hy
      · intro hy
        have e : (mkO g')⁻¹ * (mkO g' * mkO y_c * (mkO g')⁻¹) * mkO g' = mkO y_c := by group
        rw [← e, hcentr' _ hy]
        exact hy
    have hmemV₁ : ∀ y : X, y ∈ V₁c.map C.subtype ↔ ∃ h : y ∈ C, (⟨y, h⟩ : ↥C) ∈ V₁c := by
      intro y
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c.2, hc⟩
      · rintro ⟨h, hy⟩
        exact ⟨_, hy, rfl⟩
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨hyC, hy'⟩ := (hmemV₁ y).mp hy
      have := (key ⟨y, hyC⟩).mp hy'
      exact (hmemV₁ _).mpr ⟨mul_mem (mul_mem hgC hyC) (inv_mem hgC), this⟩
    · intro hy
      obtain ⟨hgyC, hgy'⟩ := (hmemV₁ _).mp hy
      have hyC : y ∈ C := by
        have := mul_mem (mul_mem (inv_mem hgC) hgyC) hgC
        simpa [mul_assoc] using this
      refine (hmemV₁ y).mpr ⟨hyC, (key ⟨y, hyC⟩).mpr ?_⟩
      exact hgy'




theorem step2_decomp (hB : BenderBalance) {x : X} {V : Subgroup X} (hx : orderOf x = 2)
    (A : SolvAPI x V) {N : Subgroup X} (hNV : V ≤ normalizer (N : Set X))
    (hNx : x ∈ normalizer (N : Set X)) (hNP : IsPStar 2 ↥N)
    (hR : ¬ oPrimeResidualOf 2 V ≤ N) {Q : Subgroup X} (hQN : Q ≤ N) (hQ2 : IsPGroup 2 Q)
    (hQs : ∀ T : Subgroup X, T ≤ N → IsPGroup 2 T → Nat.card T ≤ Nat.card Q) :
    ∀ v ∈ V, Nat.Coprime (orderOf v) 2 → ∃ n ∈ N, ∃ c ∈ centralizer (Q : Set X), v = n * c := by
  intro v hv hv2
  obtain ⟨V₁, hvV₁, hV₁V, hV₁odd, hV₁norm⟩ := exists_odd_subgroup_of_two_prime A hv hv2
  set C : Subgroup X := centralizer ({x} : Set X) with hC
  have hVC : V ≤ C := A.hVC
  set Y : Subgroup X := N ⊔ V₁ with hY
  have hNY : N ≤ Y := le_sup_left
  have hV₁Y : V₁ ≤ Y := le_sup_right
  have hV₁N : V₁ ≤ normalizer (N : Set X) := fun a ha => hNV (hV₁V ha)
  have hYn : Y ≤ normalizer (N : Set X) := sup_le Subgroup.le_normalizer hV₁N
  have hNn : (N.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hYn
  have hconj : ∀ g : X, g ∈ normalizer (N : Set X) → (∀ u ∈ V₁, g * u = u * g) →
      ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hgN hgV y hy
    obtain ⟨n, hn, u, hu, rfl⟩ := (mem_sup_of_le_normalizer hV₁N).mp hy
    have e : g * (n * u) * g⁻¹ = (g * n * g⁻¹) * u := by
      have := hgV u hu
      calc g * (n * u) * g⁻¹ = (g * n) * (u * g⁻¹) := by group
        _ = (g * n) * (g⁻¹ * (g * u * g⁻¹)) := by group
        _ = (g * n * g⁻¹) * (g * u * g⁻¹) := by group
        _ = (g * n * g⁻¹) * u := by rw [this]; group
    rw [e]
    exact mul_mem_sup ((mem_normalizer_iff.mp hgN n).mp hn) hu
  have hxV₁ : ∀ u ∈ V₁, x * u = u * x := fun u hu => by
    have := mem_centralizer_singleton_iff.mp (hVC (hV₁V hu))
    exact this.symm
  have hxY : x ∈ normalizer (Y : Set X) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => hconj x hNx hxV₁ y hy
    · intro hy
      have hx' : x⁻¹ ∈ normalizer (N : Set X) := inv_mem hNx
      have hxu' : ∀ u ∈ V₁, x⁻¹ * u = u * x⁻¹ := fun u hu => by
        have := hxV₁ u hu
        calc x⁻¹ * u = x⁻¹ * (u * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * u) * x⁻¹ := by rw [this]
          _ = u * x⁻¹ := by group
      have := hconj x⁻¹ hx' hxu' _ hy
      simpa [mul_assoc] using this
  have hMnorm : ∀ m ∈ V ⊓ Y, m ∈ normalizer (V₁ : Set X) := by
    rintro m ⟨hmV, hmY⟩
    obtain ⟨n, hn, u, hu, rfl⟩ := (mem_sup_of_le_normalizer hV₁N).mp hmY
    have hnV : n ∈ V := by
      have := V.mul_mem hmV (V.inv_mem (hV₁V hu))
      simpa using this
    have hcm := A.central_mod N hNV hR n ⟨hn, hnV⟩
    exact mul_mem (hV₁norm n hnV hcm) (Subgroup.le_normalizer hu)
  have hMW : V ⊓ Y ≤ C ⊓ Y := inf_le_inf_right Y hVC
  have hMsub : ((V ⊓ Y).subgroupOf (C ⊓ Y)).IsSubnormal := by
    have h1 := A.V_subnormal.comap (Subgroup.inclusion (inf_le_left : C ⊓ Y ≤ C))
    have e : (V ⊓ Y).subgroupOf (C ⊓ Y) =
        (V.subgroupOf C).comap (Subgroup.inclusion (inf_le_left : C ⊓ Y ≤ C)) := by
      ext g
      constructor
      · intro hg; exact hg.1
      · intro hg; exact ⟨hg, g.2.2⟩
    rw [e]; exact h1
  have hV₁M : V₁ ≤ V ⊓ Y := le_inf hV₁V hV₁Y
  have hV₁O : V₁ ≤ pPrimeCoreOf 2 (C ⊓ Y) :=
    le_pPrimeCoreOf_of_normal_subnormal hMW hMsub hV₁M hMnorm hV₁odd
  have hYle : Y ≤ N ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set X) ⊓ Y) :=
    sup_le_sup_left hV₁O N
  have hYP : IsPStar 2 ↥Y := hB X Y N x hx hxY hNY hNn hNP hYle
  have hvY : v ∈ Y := hV₁Y hvV₁
  obtain ⟨n, hn, c, ⟨-, hc⟩, hnc⟩ :=
    IsPStar.exists_mul_centralizer hYP hNY hNn hQN hQ2 hQs v hvY
  exact ⟨n, hn, c, hc, hnc⟩


end CFSG.GH74.GLS.Balance
