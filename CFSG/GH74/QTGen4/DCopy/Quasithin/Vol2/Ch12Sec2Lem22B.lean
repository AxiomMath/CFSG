module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem22A
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22B

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

namespace Lem22

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V H P : Subgroup G} {p : ℕ}

theorem eq_of_le_normalizer_F4 (h331 : Stmt3_3_1_F4) (hyp : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hp : p.Prime) (hp2 : p ≠ 2)
    (hPp : IsPGroup p ↥P) (hPH : P ≤ H) (hPM : P ⊓ Subgroup.normalizer (L : Set G) = ⊥)
    {S : Subgroup G} (hSP : S ≤ P) (hS1 : S ≠ ⊥)
    (hTS : T ≤ Subgroup.normalizer ((S ⊔ pCoreOf 2 H : Subgroup G) : Set G)) : S = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin := Lem7.minParabolic_F4 h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hT2 : IsPGroup 2 ↥T := hmin.isSylow.2.1
  set N₂ := S ⊔ pCoreOf 2 H with hN₂
  have hN₂H : N₂ ≤ H := sup_le (hSP.trans hPH) (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hK : N₂ ⊔ T = H := by
    refine hmin.eq_of_not_le le_sup_right (sup_le hN₂H hTH) fun hle => hS1 ?_
    rw [eq_bot_iff, ← hPM]
    intro x hx
    exact ⟨hSP hx, (hle (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))).2⟩
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left N₂ T hTS
  have hSQ : S ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (hSP.trans hPH).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hset2 := Subgroup.coe_mul_of_left_le_normalizer_right S (pCoreOf 2 H) hSQ
  refine le_antisymm hSP fun x hx => ?_
  have hxK : x ∈ ((N₂ ⊔ T : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, hK]
    exact hPH hx
  rw [hset] at hxK
  obtain ⟨n, hn, t, ht, hnt⟩ := hxK
  have hnt' : n * t = x := hnt
  obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨n', hn', hpow⟩ := A4.exists_pow_mul_eq hn (hTS ht) (p ^ k)
  have htN : t ^ p ^ k ∈ N₂ := by
    have e : t ^ p ^ k = n'⁻¹ := by
      rw [hnt', hk'] at hpow
      exact (eq_inv_of_mul_eq_one_right hpow.symm)
    rw [e]
    exact N₂.inv_mem hn'
  obtain ⟨j, hj⟩ := hT2 ⟨t, ht⟩
  have hj' : t ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (orderOf t) (p ^ k) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hj')
      (Nat.coprime_pow_primes j k Nat.prime_two hp (Ne.symm hp2))
  have htN₂ : t ∈ N₂ := B6.mem_of_pow_mem_of_coprime htN hcop
  have hxN : x ∈ ((S ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    rw [← hnt']
    exact N₂.mul_mem hn htN₂
  rw [hset2] at hxN
  obtain ⟨s, hs, q, hq, hsq⟩ := hxN
  have hsq' : s * q = x := hsq
  have hqP : q ∈ P := by
    have e : q = s⁻¹ * x := by rw [← hsq']; group
    rw [e]
    exact P.mul_mem (P.inv_mem (hSP hs)) hx
  have hq1 : q = 1 :=
    eq_one_of_mem_of_mem hp hp2 hPp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hqP hq
  rw [← hsq', hq1, mul_one]
  exact hs

theorem exists_inv_conj_F4 (h331 : Stmt3_3_1_F4) (hyp : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hsol : Group.IsSolvable ↥H)
    (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P) (hPH : P ≤ H)
    (hPi : ¬ p ∣ P.relIndex H) (hHPT : H = P ⊔ T)
    (hPM : P ⊓ Subgroup.normalizer (L : Set G) = ⊥) (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hidx : (V ⊓ pCoreOf 2 H).relIndex V = 2) (hP1 : P ≠ ⊥) {v : G} (hvV : v ∈ V)
    (hv2 : v ^ 2 = 1) (hvO : v ∉ pCoreOf 2 H) :
    ∃ n : G, n * v⁻¹ ∈ pCoreOf 2 H ∧ n ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ x ∈ P, n * x * n⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin := Lem7.minParabolic_F4 h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hvH : v ∈ H := hTH (hVT hvV)
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hOH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hconjO : ∀ g ∈ H, ∀ y ∈ pCoreOf 2 H, g * y * g⁻¹ ∈ pCoreOf 2 H := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hHO hg) y).mp hy
  have hPO : ∀ y ∈ P, y ∈ pCoreOf 2 H → y = 1 := fun y hyP hyO =>
    eq_one_of_mem_of_mem hp hp2 hPp hO2 hyP hyO
  obtain ⟨q, hq, hqv⟩ :=
    exists_mul_mem_normalizer_F4 h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hvH
  obtain ⟨n, hn⟩ : ∃ n : G, n = q * v := ⟨_, rfl⟩
  rw [← hn] at hqv
  have hqH : q ∈ H := hOH hq
  have hnH : n ∈ H := hn ▸ H.mul_mem hqH hvH
  have hnP : ∀ x ∈ P, n * x * n⁻¹ ∈ P := fun x hx => (Subgroup.mem_normalizer_iff.mp hqv x).mp hx
  have hn2O : n * n ∈ pCoreOf 2 H := by
    have e : n * n = q * (v * q * v⁻¹) * (v * v) := by rw [hn]; group
    rw [e, ← pow_two v, hv2, mul_one]
    exact Subgroup.mul_mem _ hq (hconjO v hvH q hq)
  have hn2c : ∀ x ∈ P, (n * n) * x * (n * n)⁻¹ = x := by
    intro x hx
    have h1 : (n * n) * x * (n * n)⁻¹ * x⁻¹ ∈ P := by
      have e : (n * n) * x * (n * n)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ := by group
      rw [e]
      exact P.mul_mem (hnP _ (hnP x hx)) (P.inv_mem hx)
    have h2 : (n * n) * x * (n * n)⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
      have e : (n * n) * x * (n * n)⁻¹ * x⁻¹ = (n * n) * (x * (n * n)⁻¹ * x⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hn2O (hconjO x (hPH hx) _ (Subgroup.inv_mem _ hn2O))
    exact mul_inv_eq_one.mp (hPO _ h1 h2)
  have htn : ∀ t ∈ T, t * n * t⁻¹ * n⁻¹ ∈ pCoreOf 2 H := by
    intro t ht
    have htv : t * v * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hTV ht) v).mp hvV
    have htvO : t * v * t⁻¹ ∉ pCoreOf 2 H := fun h0 => hvO (by
      have := hconjO t⁻¹ (H.inv_mem (hTH ht)) _ h0
      simpa [mul_assoc] using this)
    have hmul : t * v * t⁻¹ * v⁻¹ ∈ pCoreOf 2 H := by
      have h1 : (⟨t * v * t⁻¹, htv⟩ : ↥V) * ⟨v⁻¹, V.inv_mem hvV⟩ ∈
          (V ⊓ pCoreOf 2 H).subgroupOf V := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        refine iff_of_false (fun h0 => htvO (Subgroup.mem_subgroupOf.mp h0).2) fun h0 => hvO ?_
        have := Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp h0).2
        simpa using this
      exact (Subgroup.mem_subgroupOf.mp h1).2
    have e : t * n * t⁻¹ * n⁻¹ = (t * q * t⁻¹) * (t * v * t⁻¹ * v⁻¹) * q⁻¹ := by
      rw [hn]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hconjO t (hTH ht) q hq) hmul)
      (Subgroup.inv_mem _ hq)
  set S := P ⊓ Subgroup.centralizer ({n} : Set G) with hS
  have hOn : ((pCoreOf 2 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mpr hHO
  have hTS : T ≤ Subgroup.normalizer ((S ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro t ht
    have htH := hTH ht
    refine Sec121Swap.mem_normalizer_of_conj_mem fun y hy => ?_
    have hSQ : S ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := (inf_le_left.trans hPH).trans hHO
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right S (pCoreOf 2 H) hSQ
    rw [← SetLike.mem_coe, hset] at hy
    obtain ⟨s, hs, o, ho, hso⟩ := hy
    have hso' : s * o = y := hso
    have hts : t * s * t⁻¹ ∈ P ⊔ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_sup_F4 h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 htH) s).mp
        (Subgroup.mem_sup_left hs.1)
    have hPQ : P ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := hPH.trans hHO
    have hset2 := Subgroup.coe_mul_of_left_le_normalizer_right P (pCoreOf 2 H) hPQ
    rw [← SetLike.mem_coe, hset2] at hts
    obtain ⟨x', hx', o', ho', hxo⟩ := hts
    have hxo' : x' * o' = t * s * t⁻¹ := hxo
    have hx'S : x' ∈ S := by
      refine ⟨hx', Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hsH := hPH hs.1
      have hx'H := hPH hx'
      have hsn : s * n = n * s := Subgroup.mem_centralizer_singleton_iff.mp hs.2
      have hw : (⟨n, hnH⟩ : ↥H) * ⟨x', hx'H⟩ * (⟨n, hnH⟩ : ↥H)⁻¹ * (⟨x', hx'H⟩ : ↥H)⁻¹ ∈
          (pCoreOf 2 H).subgroupOf H :=
        comm_mem_of_mem (O := (pCoreOf 2 H).subgroupOf H) (o' := ⟨o', hOH ho'⟩)
          (t := ⟨t, htH⟩) (s := ⟨s, hsH⟩) (Subgroup.mem_subgroupOf.mpr (htn t ht))
          (Subtype.ext hsn) (Subtype.ext hxo'.symm) (Subgroup.mem_subgroupOf.mpr ho')
      have hwO : n * x' * n⁻¹ * x'⁻¹ ∈ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp hw
      have hwP : n * x' * n⁻¹ * x'⁻¹ ∈ P := P.mul_mem (hnP x' hx') (P.inv_mem hx')
      have h1 : n * x' * n⁻¹ = x' := mul_inv_eq_one.mp (hPO _ hwP hwO)
      calc x' * n = (n * x' * n⁻¹) * n := by rw [h1]
        _ = n * x' := by group
    have e : t * y * t⁻¹ = (t * s * t⁻¹) * (t * o * t⁻¹) := by
      rw [← hso']
      group
    rw [e, ← hxo', mul_assoc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx'S)
      (Subgroup.mem_sup_right (Subgroup.mul_mem _ ho' (hconjO t htH o ho)))
  have hSbot : S = ⊥ := by
    by_contra hne
    have hSP := eq_of_le_normalizer_F4 h331 hyp hHs hp hp2 hPp hPH hPM inf_le_left hne hTS
    have hxv : ∀ x ∈ P, x * v * x⁻¹ * v⁻¹ ∈ pCoreOf 2 H := by
      intro x hx
      have hxS : x ∈ S := by rw [hS, hSP]; exact hx
      have hxn : x * n = n * x := Subgroup.mem_centralizer_singleton_iff.mp hxS.2
      have hv : v = q⁻¹ * n := by rw [hn]; group
      have e : x * v * x⁻¹ * v⁻¹ = (x * q⁻¹ * x⁻¹) * q := by
        rw [hv]
        calc x * (q⁻¹ * n) * x⁻¹ * (q⁻¹ * n)⁻¹ = x * q⁻¹ * x⁻¹ * (x * n) * x⁻¹ * n⁻¹ * q := by
              group
          _ = x * q⁻¹ * x⁻¹ * (n * x) * x⁻¹ * n⁻¹ * q := by rw [hxn]
          _ = (x * q⁻¹ * x⁻¹) * q := by group
      rw [e]
      exact Subgroup.mul_mem _ (hconjO x (hPH hx) _ (Subgroup.inv_mem _ hq)) hq
    set Y := pCoreOf 2 H ⊔ V with hY
    have hYT : Y ≤ T := sup_le (pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow) hVT
    have hYp : IsPGroup 2 ↥Y := hmin.isSylow.2.1.to_le hYT
    have hYH : Y ≤ H := hYT.trans hTH
    have hPY : P ≤ Subgroup.normalizer (Y : Set G) := by
      intro x hx
      have hxH := hPH hx
      have hmapY : Y.map (MulAut.conj x).toMonoidHom ≤ Y := by
        rw [hY, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨w, hw, rfl⟩
          exact Subgroup.mem_sup_left (hconjO x hxH w hw)
        · rintro _ ⟨w, hw, rfl⟩
          show x * w * x⁻¹ ∈ Y
          by_cases hwO : w ∈ pCoreOf 2 H
          · exact Subgroup.mem_sup_left (hconjO x hxH w hwO)
          · have h1 : (⟨w, hw⟩ : ↥V) * ⟨v⁻¹, V.inv_mem hvV⟩ ∈
                (V ⊓ pCoreOf 2 H).subgroupOf V := by
              rw [Subgroup.mul_mem_iff_of_index_two hidx]
              refine iff_of_false (fun h0 => hwO (Subgroup.mem_subgroupOf.mp h0).2)
                fun h0 => hvO ?_
              have := Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp h0).2
              simpa using this
            have hwv : w * v⁻¹ ∈ pCoreOf 2 H := (Subgroup.mem_subgroupOf.mp h1).2
            have e : x * w * x⁻¹ = (x * (w * v⁻¹) * x⁻¹) * (x * v * x⁻¹ * v⁻¹) * v := by
              group
            rw [e]
            exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _
              (hconjO x hxH _ hwv) (hxv x hx))) (Subgroup.mem_sup_right hvV)
      exact Sec121Swap.mem_normalizer_of_conj_mem fun y hy => hmapY ⟨y, hy, rfl⟩
    have hTY : T ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
      Lem21Post.mem_normalizer_sup (hHO (hTH ht)) (hTV ht)
    have hHY : H ≤ Subgroup.normalizer (Y : Set G) := by
      rw [hHPT]
      exact sup_le hPY hTY
    have hYO : Y ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYH hHY hYp
    exact hvO (hYO (Subgroup.mem_sup_right hvV))
  refine ⟨n, by rw [hn, mul_inv_cancel_right]; exact hq, hqv, fun x hx => ?_⟩
  have hnx := hnP x hx
  have hyS : x * (n * x * n⁻¹) ∈ S := by
    refine ⟨P.mul_mem hx hnx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : n * (x * (n * x * n⁻¹)) * n⁻¹ = x * (n * x * n⁻¹) := by
      calc n * (x * (n * x * n⁻¹)) * n⁻¹ = (n * x * n⁻¹) * ((n * n) * x * (n * n)⁻¹) := by
            group
        _ = (n * x * n⁻¹) * x := by rw [hn2c x hx]
        _ = x * (n * x * n⁻¹) := hPc _ hnx _ hx
    calc x * (n * x * n⁻¹) * n = (n * (x * (n * x * n⁻¹)) * n⁻¹) * n := by rw [h1]
      _ = n * (x * (n * x * n⁻¹)) := by group
  rw [hSbot, Subgroup.mem_bot] at hyS
  exact eq_inv_of_mul_eq_one_right hyS

end Lem22

end CFSG.Quasithin.H13
