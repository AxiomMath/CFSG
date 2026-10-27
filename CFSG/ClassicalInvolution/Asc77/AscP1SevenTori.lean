module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenBurnside
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenBasic
public import CFSG.ClassicalInvolution.Asc77.AscT3Sym

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem inf_centralizer_le_normalizer' (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {j : G}
    (hj : IsUniqueInvolution J j) {U V : Subgroup G}
    (hU : IsSylow2In U (K ⊓ Subgroup.centralizer ({j} : Set G))) (hUc : IsCyclic ↥U)
    (hU4 : 4 ≤ Nat.card U) (hVJ : V ≤ J) (hV2 : IsPGroup 2 ↥V) (hV4 : 4 ≤ Nat.card V)
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) (hVj : V ≤ Subgroup.centralizer ({j} : Set G)) :
    K ⊓ Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  set H := K ⊓ Subgroup.centralizer ({j} : Set G) with hH
  obtain ⟨N₀, hN₀H, hN₀odd, hdec, hoddmem⟩ := exists_odd_complement_of_isCyclic hU hUc
  have hconjj : ∀ h ∈ H, IsUniqueInvolution (conjSub h J) j := by
    intro h hh
    have h1 := hj.conj h
    have e : h * j * h⁻¹ = j := by
      have h2 : h * j = j * h := Subgroup.mem_centralizer_singleton_iff.mp hh.2
      calc h * j * h⁻¹ = j * h * h⁻¹ := by rw [h2]
        _ = j := by group
    rwa [e] at h1
  have hU2 : IsPGroup 2 ↥U := hU.2.1
  have hUK : U ≤ K := hU.1.trans inf_le_left
  have hUj : U ≤ Subgroup.centralizer ({j} : Set G) := hU.1.trans inf_le_right
  have hUN : U ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hJ hK hKJ.symm hj hUK hU2 (by omega) hUj
  have hVconj : ∀ h ∈ H, V ≤ Subgroup.normalizer ((conjSub h J : Subgroup G) : Set G) := by
    intro h hh
    by_cases he : conjSub h J = J
    · rw [he]
      exact hVJ.trans Subgroup.le_normalizer
    · exact hΩ.le_normalizer_of_le_centralizer hp hq (hΩ.conjInvariant h J hJ) hJ he
        (hconjj h hh) hVJ hV2 (by omega) hVj
  have hVN₀ : ∀ v ∈ V, ∀ n ∈ N₀, v * n * v⁻¹ ∈ N₀ := by
    intro v hv n hn
    have hnH := hN₀H hn
    have hmemH : v * n * v⁻¹ ∈ H :=
      ⟨(Subgroup.mem_normalizer_iff.mp (hVK hv) n).mp hnH.1,
        (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem (hVj hv) hnH.2)
          ((Subgroup.centralizer _).inv_mem (hVj hv))⟩
    have hodd : Odd (orderOf (v * n * v⁻¹)) := by
      have e : orderOf (v * n * v⁻¹) = orderOf n := by
        simpa [MulAut.conj_apply] using (MulAut.conj v).orderOf_eq n
      rw [e]
      exact hN₀odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N₀ hn)
    exact hoddmem _ hmemH hodd
  have hN₀N : ∀ w ∈ N₀, w ∈ Subgroup.normalizer (J : Set G) := by
    intro w hw
    set N₁ : Subgroup G := N₀ ⊓ Subgroup.normalizer (J : Set G) with hN₁
    set C : Set G := {c | w⁻¹ * c ∈ N₁} with hC
    have hwconj : ∀ v ∈ V, w⁻¹ * v * w ∈ Subgroup.normalizer (J : Set G) := by
      intro v hv
      have := hVconj w (hN₀H hw) hv
      rwa [mem_normalizer_conjSub_iff] at this
    have hVJN : ∀ v ∈ V, v ∈ Subgroup.normalizer (J : Set G) := fun v hv =>
      Subgroup.le_normalizer (hVJ hv)
    have hCstable : ∀ v ∈ V, ∀ c ∈ C, v * c * v⁻¹ ∈ C := by
      intro v hv c hc
      have e : w⁻¹ * (v * c * v⁻¹) = (w⁻¹ * (v * w * v⁻¹)) * (v * (w⁻¹ * c) * v⁻¹) := by group
      show w⁻¹ * (v * c * v⁻¹) ∈ N₁
      rw [e]
      refine N₁.mul_mem ⟨N₀.mul_mem (N₀.inv_mem hw) (hVN₀ v hv w hw), ?_⟩
        ⟨hVN₀ v hv _ hc.1, ?_⟩
      · have e2 : w⁻¹ * (v * w * v⁻¹) = (w⁻¹ * v * w) * v⁻¹ := by group
        rw [e2]
        exact (Subgroup.normalizer _).mul_mem (hwconj v hv)
          ((Subgroup.normalizer _).inv_mem (hVJN v hv))
      · exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem (hVJN v hv) hc.2)
          ((Subgroup.normalizer _).inv_mem (hVJN v hv))
    have hCcard : Nat.card C = Nat.card N₁ := by
      refine Nat.card_congr ⟨fun c => ⟨w⁻¹ * c, c.2⟩, fun n => ⟨w * n, ?_⟩, ?_, ?_⟩
      · show w⁻¹ * (w * n) ∈ N₁
        simp
      · intro c
        apply Subtype.ext
        show w * (w⁻¹ * c) = c
        group
      · intro n
        apply Subtype.ext
        show w⁻¹ * (w * n) = n
        group
    have hCodd : Odd (Nat.card C) := by
      rw [hCcard]
      exact hN₀odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    obtain ⟨c, hcC, hcfix⟩ := exists_fixed_mem_of_odd hV2 hCstable hCodd
    have hVc : V ≤ conjSub c J := by
      intro v hv
      have h1 := hcfix v hv
      rw [mem_conjSub_iff]
      have hvc : v * c = c * v := by
        calc v * c = v * c * v⁻¹ * v := by group
          _ = c * v := by rw [h1]
      have e : c⁻¹ * v * c = v := by
        calc c⁻¹ * v * c = c⁻¹ * (v * c) := by group
          _ = c⁻¹ * (c * v) := by rw [hvc]
          _ = v := by group
      rw [e]
      exact hVJ hv
    have hJc : conjSub c J = J :=
      hΩ.eq_of_le_of_le (hΩ.conjInvariant c J hJ) hJ hV2 hV4 hVc hVJ
    have hcN : c ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_iff_conjSub_eq.mpr hJc
    have hwc : w⁻¹ * c ∈ Subgroup.normalizer (J : Set G) := hcC.2
    have hwinv : w⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
      have := (Subgroup.normalizer _).mul_mem hwc ((Subgroup.normalizer _).inv_mem hcN)
      simpa using this
    simpa using (Subgroup.normalizer _).inv_mem hwinv
  intro h hh
  obtain ⟨n, hn, u, hu, rfl⟩ := hdec h hh
  exact (Subgroup.normalizer _).mul_mem (hN₀N n hn) (hUN hu)

theorem isSylow2In_inf_W_centralizer (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K)
    (hTJ : IsSylow2In T J) (hnot : J ∉ omegaNbr Ω K) {j : G} (hj : IsUniqueInvolution J j) :
    IsSylow2In (K ⊓ W) (K ⊓ Subgroup.centralizer ({j} : Set G)) := by
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  have hjW : j ∈ J ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hJ hT hTJ hj
  obtain ⟨hRWeq, -, -, -, hcard⟩ := inf_W_of_mem_D hp hq hΩ hW hR hK hRK
  have hKW2 : IsPGroup 2 ↥(K ⊓ W) := (isPGroup_of_mem_WSet hW).to_inf_right
  have hle : K ⊓ W ≤ K ⊓ Subgroup.centralizer ({j} : Set G) := fun x hx =>
    ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr (hWab x hx.2 j hjW.2)⟩
  obtain ⟨V₀, hV₀, hKWV₀⟩ := IsSylow2In.exists_ge hKW2 hle
  obtain ⟨R', hR', hV₀R'⟩ := IsSylow2In.exists_ge hV₀.2.1 (hV₀.1.trans inf_le_left)
  have hRR' : Nat.card R = Nat.card R' := hRK.natCard_eq hR'
  have hKWcard : Nat.card ↥(K ⊓ W) = Nat.card ↥(R ⊓ W) := by rw [hRWeq]
  have hd1 : Nat.card ↥(K ⊓ W) ∣ Nat.card V₀ := Subgroup.card_dvd_of_le hKWV₀
  have hd2 : Nat.card V₀ ∣ Nat.card R' := Subgroup.card_dvd_of_le hV₀R'
  obtain ⟨m, hm⟩ := hd1
  have ha0 : 0 < Nat.card ↥(K ⊓ W) := Nat.card_pos
  have hR'a : Nat.card R' = Nat.card ↥(K ⊓ W) * 2 := by
    rw [← hRR', hcard, ← hKWcard, mul_comm]
  have hm2 : m ∣ 2 := by
    rw [hR'a, hm] at hd2
    exact Nat.dvd_of_mul_dvd_mul_left ha0 hd2
  rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h1 | h2
  · have hc : Nat.card V₀ = Nat.card ↥(K ⊓ W) := by rw [hm, h1, mul_one]
    have heq : K ⊓ W = V₀ := Subgroup.eq_of_le_of_card_ge hKWV₀ hc.le
    rw [heq]
    exact hV₀
  · exfalso
    have hcardV₀ : Nat.card V₀ = Nat.card R' := by rw [hm, h2, hR'a]
    have hV₀eq : V₀ = R' := Subgroup.eq_of_le_of_card_ge hV₀R' hcardV₀.ge
    have hR'c : R' ≤ Subgroup.centralizer ({j} : Set G) := hV₀eq ▸ hV₀.1.trans inf_le_right
    have h8 : 8 ≤ Nat.card R' := by
      rw [← hRR']
      exact hΩ.eight_le_of_mem_RSet hp hR.1
    have hR'N : R' ≤ Subgroup.normalizer (J : Set G) :=
      hΩ.le_normalizer_of_le_centralizer hp hq hJ hK hKJ.symm hj hR'.1 hR'.2.1 (by omega) hR'c
    have hKnbr : K ∈ omegaNbr Ω J := ⟨hK, hKJ, R', mem_RSet_of_isSylow2In hK hR', hR'.1, hR'N⟩
    exact hnot (T3.omegaNbr_symm h62 hp hq hΩ hJ hK hKnbr)

theorem inf_centralizer_le_normalizer_of_D (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K)
    (hTJ : IsSylow2In T J) (hnot : J ∉ omegaNbr Ω K) {j : G} (hj : IsUniqueInvolution J j) :
    K ⊓ Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  have hSyl := isSylow2In_inf_W_centralizer h62 hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hj
  obtain ⟨hRWeq, -, hcyc, h4, -⟩ := inf_W_of_mem_D hp hq hΩ hW hR hK hRK
  obtain ⟨hTWeq, -, -, hV4, -⟩ := inf_W_of_mem_D hp hq hΩ hW hT hJ hTJ
  refine inf_centralizer_le_normalizer' hp hq hΩ hK hJ hKJ hj hSyl ?_ ?_ inf_le_left
    (isPGroup_of_mem_WSet hW).to_inf_right ?_
    (inf_W_le_normalizer_of_ne hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ).2 ?_
  · rw [← hRWeq]
    exact hcyc
  · rw [← hRWeq]
    exact h4
  · rw [← hTWeq]
    exact hV4
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hj.commute_of_mem hx.1).symm

end Thompson

end CFSG.ClassicalInvolution.Asc77
