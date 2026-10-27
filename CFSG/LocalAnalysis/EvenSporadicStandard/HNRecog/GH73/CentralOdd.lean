module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

private lemma eq_of_mem_of_card_two {G : Type*} [Group G] {H : Subgroup G}
    (hH : Nat.card H = 2) {a b : G} (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a = b := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥H)).mp hH
  have h1 : (⟨a, ha⟩ : ↥H) = y :=
    huniq ⟨a, ha⟩ (fun h => ha1 (by simpa using congrArg Subtype.val h))
  have h2 : (⟨b, hb⟩ : ↥H) = y :=
    huniq ⟨b, hb⟩ (fun h => hb1 (by simpa using congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem eq_of_central_odd_section {X : Type*} [Group X] [Finite X] (V M : Subgroup X)
    [V.Normal] [M.Normal] (hVM : V ≤ M) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hcent : ∀ x : X, (∀ v ∈ V, v * x = x * v) → x ∈ V)
    (hMX : ∀ m ∈ M, ∀ x : X, m * x * m⁻¹ * x⁻¹ ∈ V) (hodd : Odd (V.relIndex M))
    (S : Sylow 2 X) (hVS : V ≤ (S : Subgroup X))
    (hZ : Nat.card (Subgroup.center ↥(S : Subgroup X)) = 2) : M = V := by
  by_contra hne
  have hwit : V.relIndex M ≠ 1 := by
    intro h
    exact hne (le_antisymm hVM (Subgroup.relIndex_eq_one.mp h)).symm
  obtain ⟨p, hpprime, hp_dvd_rel⟩ := Nat.exists_prime_and_dvd hwit
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have h2 : 2 ∣ V.relIndex M := hp2 ▸ hp_dvd_rel
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hp_dvd_card : p ∣ Nat.card M := hp_dvd_rel.trans (Subgroup.relIndex_dvd_card V M)
  obtain ⟨gm, hgm_order⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) p hp_dvd_card
  let g : X := (gm : X)
  have hgM : g ∈ M := gm.2
  have hg_order : orderOf g = p := (Subgroup.orderOf_coe gm).trans hgm_order
  have hg_ne_one : g ≠ 1 := by
    intro h
    have : orderOf g = 1 := by rw [h]; exact orderOf_one
    rw [hg_order] at this
    exact hpprime.ne_one this
  set A : Subgroup X := Subgroup.zpowers g with hA
  have hgA : g ∈ A := by rw [hA]; exact Subgroup.mem_zpowers g
  have hA_le_M : A ≤ M := by rw [hA]; exact Subgroup.zpowers_le.mpr hgM
  have hcardA : Nat.card A = p := by rw [hA, Nat.card_zpowers, hg_order]
  have hVp : IsPGroup 2 V := S.isPGroup'.to_le hVS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    rw [hcardA, hn]
    simpa using Nat.coprime_pow_primes 1 n hpprime Nat.prime_two hp_ne_two
  have hAN : A ≤ Subgroup.normalizer (V : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hVab' : ∀ x y : ↥V, x * y = y * x := fun x y => Subtype.ext (hVab x.1 x.2 y.1 y.2)
  haveI : Finite ↥V := Finite.of_injective (Subtype.val : ↥V → X) Subtype.val_injective
  haveI : Finite ↥A := Finite.of_injective (Subtype.val : ↥A → X) Subtype.val_injective
  obtain ⟨-, hdisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp V A hAN hVab' hcop
  set W : Subgroup X := ⁅V, A⁆ with hW
  have hWV : W ≤ V := by
    rw [hW]
    exact Subgroup.commutator_le_left (H₁ := V) (H₂ := A)
  have hgV : g ∉ V := by
    intro hgVmem
    have hdvd : p ∣ 2 ^ n := hn ▸ (hg_order ▸ Subgroup.orderOf_dvd_natCard V hgVmem)
    have hp_dvd_two : p ∣ 2 := hpprime.dvd_of_dvd_pow hdvd
    exact hp_ne_two ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp hp_dvd_two)
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hbot0 : ⁅V, A⁆ = ⊥ := by rw [hW] at hbot; exact hbot
    have hAcent : A ≤ Subgroup.centralizer (V : Set X) := by
      have hcomm : ⁅A, V⁆ = ⊥ := by rw [Subgroup.commutator_comm A V]; exact hbot0
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hgcent : ∀ v ∈ V, v * g = g * v := by
      have hmem : g ∈ Subgroup.centralizer (V : Set X) := hAcent hgA
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact hmem
    exact hgV (hcent g hgcent)
  have hVV : ⁅V, V⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hVab v hv w hw).symm
  have hWnormal : W.Normal := by
    refine ⟨fun n hn x => ?_⟩
    have hmap : W.map (MulAut.conj x : X →* X) ≤ W := by
      have hVmap : V.map (MulAut.conj x : X →* X) = V :=
        Subgroup.normal_iff_map_conj_eq.mp (inferInstance : V.Normal) x
      have hAmap : A.map (MulAut.conj x : X →* X) ≤ V ⊔ A := by
        rw [hA, MonoidHom.map_zpowers]
        refine Subgroup.zpowers_le.mpr ?_
        have hmem : (g * x * g⁻¹ * x⁻¹)⁻¹ * g ∈ V ⊔ A :=
          (V ⊔ A).mul_mem ((V ⊔ A).inv_mem (Subgroup.mem_sup_left (hMX g hgM x)))
            (Subgroup.mem_sup_right hgA)
        convert hmem using 1
        show x * g * x⁻¹ = (g * x * g⁻¹ * x⁻¹)⁻¹ * g
        group
      calc W.map (MulAut.conj x : X →* X)
          = ⁅V, A⁆.map (MulAut.conj x : X →* X) := by rw [hW]
        _ = ⁅V.map (MulAut.conj x : X →* X), A.map (MulAut.conj x : X →* X)⁆ :=
              Subgroup.map_commutator V A (MulAut.conj x : X →* X)
        _ = ⁅V, A.map (MulAut.conj x : X →* X)⁆ := by rw [hVmap]
        _ ≤ ⁅V, V ⊔ A⁆ := Subgroup.commutator_mono_right hAmap
        _ = ⁅V, V⁆ ⊔ ⁅V, A⁆ := Subgroup.commutator_sup_left V V A
        _ = W := by rw [hVV, hW]; simp
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj x : X →* X) hn
    exact hmap hmem
  haveI : W.Normal := hWnormal
  set GS : Subgroup X := (S : Subgroup X) with hGS
  haveI : Group.IsNilpotent ↥GS := S.isPGroup'.isNilpotent
  have hGWne : W.subgroupOf GS ≠ ⊥ := by
    intro h
    apply hWne
    rw [eq_bot_iff]
    intro w hw
    have hmem : (⟨w, hVS (hWV hw)⟩ : ↥GS) ∈ W.subgroupOf GS := by
      rw [Subgroup.mem_subgroupOf]; exact hw
    rw [h] at hmem
    have hw1 : (⟨w, hVS (hWV hw)⟩ : ↥GS) = 1 := Subgroup.mem_bot.mp hmem
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hw1)
  have hinf : (W.subgroupOf GS) ⊓ Subgroup.center ↥GS ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥GS) (H := W.subgroupOf GS) hGWne
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  let z : X := ((y : ↥GS) : X)
  have hzW : z ∈ W := by
    change ((y : ↥GS) : X) ∈ W
    exact Subgroup.mem_subgroupOf.mp y.2.1
  have hzV : z ∈ V := hWV hzW
  have hzS : z ∈ GS := hVS hzV
  have hzC : ∀ s ∈ GS, s * z = z * s := by
    intro s hs
    have h := Subgroup.mem_center_iff.mp y.2.2 (⟨s, hs⟩ : ↥GS)
    simpa [z] using congrArg Subtype.val h
  have hz1 : z ≠ 1 := by
    intro h
    apply hy1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  let z' : X := g * z * g⁻¹
  have hz'V : z' ∈ V := (inferInstance : V.Normal).conj_mem z hzV g
  have hz'S : z' ∈ GS := hVS hz'V
  have hz'C : ∀ s ∈ GS, s * z' = z' * s := by
    intro s hs
    have key : s * z' * s⁻¹ = z' := by
      have hwV : (g * s * g⁻¹ * s⁻¹)⁻¹ ∈ V := V.inv_mem (hMX g hgM s)
      have hsz : s * z * s⁻¹ = z := by rw [hzC s hs]; group
      have hsg : s * g * s⁻¹ = (g * s * g⁻¹ * s⁻¹)⁻¹ * g := by group
      have h1 : s * z' * s⁻¹ = (s * g * s⁻¹) * (s * z * s⁻¹) * (s * g * s⁻¹)⁻¹ := by
        simp only [z']; group
      rw [h1, hsg, hsz]
      have hcomm : (g * s * g⁻¹ * s⁻¹)⁻¹ * z' = z' * (g * s * g⁻¹ * s⁻¹)⁻¹ :=
        hVab ((g * s * g⁻¹ * s⁻¹)⁻¹) hwV z' hz'V
      have e : ((g * s * g⁻¹ * s⁻¹)⁻¹ * g) * z * ((g * s * g⁻¹ * s⁻¹)⁻¹ * g)⁻¹
          = (g * s * g⁻¹ * s⁻¹)⁻¹ * z' * ((g * s * g⁻¹ * s⁻¹)⁻¹)⁻¹ := by
        simp only [z']; group
      rw [e, hcomm]
      group
    calc s * z' = (s * z' * s⁻¹) * s := by group
      _ = z' * s := by rw [key]
  have hz'ne : z' ≠ 1 := by
    intro h
    apply hz1
    have hh : g * z * g⁻¹ = 1 := h
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [hh]; group
  have hz'eq : z' = z := by
    have hcenter_eq : (⟨z', hz'S⟩ : ↥GS) = ⟨z, hzS⟩ :=
      eq_of_mem_of_card_two (show Nat.card (Subgroup.center ↥GS) = 2 from hZ)
        (Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hz'C s.1 s.2))
        (Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hzC s.1 s.2))
        (fun h => hz'ne (by simpa using congrArg Subtype.val h))
        (fun h => hz1 (by simpa using congrArg Subtype.val h))
    exact congrArg Subtype.val hcenter_eq
  have hgz : g * z = z * g := by
    have : g * z * g⁻¹ = z := hz'eq
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [this]
  have hz_cenA : z ∈ Subgroup.centralizer (A : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hA] at ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact Commute.zpow_left hgz k
  have hz_in : z ∈ (V ⊓ Subgroup.centralizer (A : Set X)) ⊓ ⁅V, A⁆ :=
    ⟨⟨hzV, hz_cenA⟩, by rw [← hW]; exact hzW⟩
  exact hz1 (Subgroup.mem_bot.mp (hdisj.le_bot hz_in))

end CFSG.EvenSporadicStandard.HNRecog.GH73
