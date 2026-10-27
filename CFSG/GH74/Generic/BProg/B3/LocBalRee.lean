module

public import CFSG.GH74.Generic.BProg.B2.GenLocRee
public import CFSG.GH74.Generic.BProg.B2.FixFourS45
public import CFSG.Walter.W67.JR.OutRigid
public import CFSG.Walter.ReeOrder.JTFinal
public import CFSG.GH74.Generic.BProg.B3.Obs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5
open scoped commutatorElement

theorem isLocBal32_of_oddCore {X : Type} [Group X] (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1)
    (hodd : ∀ H : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ H →
      ∀ t : ↥H, orderOf t = 2 → CFSG.Assembly.Dichotomy.involutionOddCore t = ⊥)
    (B : Subgroup (MulAut X)) (hB : ∀ b ∈ B, b * b = 1) : IsLocBal32 X B := by
  have _hZ := hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro H hH hBH
  have hord : ∀ b : ↥H, b * b = 1 → b ≠ 1 → orderOf b = 2 := fun b hb2 hb1 =>
    orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  refine ⟨fun b hb hb1 c hc b' _ => ?_, fun D _ hcard hsq => ?_⟩
  · have hb2 : b * b = 1 := Subtype.ext (by simpa using hB _ (Subgroup.mem_subgroupOf.mp hb))
    rw [hodd H hH b (hord b hb2 hb1), Subgroup.mem_bot] at hc
    rw [hc]
    simp
  · have hne : D ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hcard
      omega
    obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    rw [eq_bot_iff]
    exact (deltaCore_le_involutionOddCore hd hd1').trans (hodd H hH d (hord d (hsq d hd) hd1')).le

namespace LocBalRee

section Ree


theorem finite_of_qShape4 {T : Type} [Group T] (h : QShape4 T) : Finite T := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨a, K, _, _, _, -, -, ⟨e⟩⟩ :=
    B1.PilotS4.ree_model_data' (B1.PilotS4.reeTitsModel_of_lieModel hf)
  have : Finite (CFSG.LieType.Ree.ReeTag.G2.reeGamma K a) := by
    have := CFSG.LieType.Chevalley.finite_modGL (τ := CFSG.LieType.Ree.ReeTag.G2.tag) (K := K)
    infer_instance
  exact Finite.of_equiv _ e.symm.toEquiv

theorem exists_jrGroup {T : Type} [Group T] [Finite T] (h : QShape4 T) {z : T} (hz : orderOf z = 2) :
    ∃ hL : CFSG.Walter.W67.JRGroup T, hL.J = z ∧ 5 < hL.q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f, -, hf3, hdat⟩ := B2.GenLocRee.ree_cent_datum h
  obtain ⟨F, hF1, hF2, hF3, ⟨iso⟩⟩ := hdat z hz
  have hE8 := (B2.FixFourS45.shape4_data h).1
  have hsimple : IsSimpleGroup T := B2.ree_isSimple h
  have hnonab : ∃ a b : T, a * b ≠ b * a := by
    have hz1 : z ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hz
      omega
    obtain ⟨y, hy⟩ := B2.ree_involution_noncentral h hz1
    exact ⟨y, z, hy⟩
  refine ⟨{ p := 3
            f := f
            p_ne_two := by norm_num
            f_pos := by omega
            index_ne_two := fun N _ => CFSG.Walter.index_ne_two_of_isSimpleGroup hnonab N
            card_sylow := fun P => (hE8.all P).2
            elementary_sylow := fun P => (hE8.all P).1
            J := z
            orderOf_J := hz
            K := F
            le_centralizer := hF1
            J_not_mem := hF2
            centralizer_eq := hF3
            iso := iso }, rfl, ?_⟩
  show 5 < 3 ^ f
  calc 5 < 3 ^ 3 := by norm_num
    _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf3

section Walter


theorem aut_eq_one_of_fixes_centralizer {T : Type} [Group T] [Finite T] (h : QShape4 T) {z : T}
    (hz : orderOf z = 2) {σ : MulAut T} (hσ : Odd (orderOf σ))
    (hfix : ∀ k : T, k * z = z * k → σ k = k) : σ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hL, hJ, hq⟩ := exists_jrGroup h hz
  have hres := hL.eq_one_or_eq_conj_J CFSG.Walter.jtThreeHyp hq σ
    (by rw [hJ]; exact hfix z rfl)
    (fun k hk => hfix k (by rw [← hJ]; exact hL.commute_J_of_mem_K hk))
  rcases hres with h1 | h2
  · exact h1
  · exfalso
    rw [hJ] at h2
    have hz2 : z ^ 2 = 1 := by
      rw [← hz]
      exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hz
      omega
    have hc2 : orderOf (MulAut.conj z : MulAut T) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow, hz2, map_one]
      · intro h1
        exact hz1 (B2.ree_conj_injective h (h1.trans (map_one _).symm))
    rw [h2, hc2] at hσ
    exact absurd hσ (by decide)

theorem involutionOddCore_eq_bot_ree {Kt : Type} [Group Kt] [Finite Kt] (hK : QShape4 Kt)
    {H : Subgroup (MulAut Kt)} (hH : (MulAut.conj : Kt →* MulAut Kt).range ≤ H) {t : ↥H}
    (ht : orderOf t = 2) : involutionOddCore t = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := B2.ree_conj_injective hK
  have ht2 : (t : MulAut Kt) * (t : MulAut Kt) = 1 := by
    have h1 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht, sq] at this
    simpa using congrArg (fun s : ↥H => (s : MulAut Kt)) h1
  obtain ⟨z, hz⟩ := B2.ree_sq_aut_inner hK ht2
  have hz2 : z * z = 1 := by
    apply hinj
    rw [map_mul, map_one, hz]
    exact ht2
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [map_one] at hz
    have h1 : t = 1 := Subtype.ext hz.symm
    rw [h1, orderOf_one] at ht
    omega
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  obtain ⟨n₀, hsplit⟩ := B1.PilotS4.splitGrp_of_qShape4 hK
  obtain ⟨L, hL⟩ := hsplit.split z hzord
  have hbotz : pPrimeCore 2 ↥(centralizer ({z} : Set Kt)) = ⊥ := hL.pPrimeCore_eq_bot
  unfold involutionOddCore
  rw [oddCore_eq_pPrimeCore]
  set C : Subgroup ↥H := centralizer ({t} : Set ↥H) with hCdef
  suffices hN : pPrimeCore 2 ↥C = ⊥ by rw [hN, Subgroup.map_bot]
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hNn : (pPrimeCore 2 ↥C).Normal := CFSG.pPrimeCore_normal
  have hNc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥C)) := CFSG.pPrimeCore_coprime_card
  set N : Subgroup ↥C := pPrimeCore 2 ↥C with hNdef
  obtain ⟨ι, hι⟩ : ∃ ι : ↥C →* MulAut Kt, ∀ c : ↥C, ι c = ((c : ↥H) : MulAut Kt) :=
    ⟨H.subtype.comp C.subtype, fun _ => rfl⟩
  have hιinj : Function.Injective ι := fun a b hab =>
    Subtype.ext (Subtype.ext (by rw [← hι a, ← hι b]; exact hab))
  have hιcomm : ∀ c : ↥C, ι c * MulAut.conj z = MulAut.conj z * ι c := by
    intro c
    have h1 : (c : ↥H) * t = t * (c : ↥H) := mem_centralizer_singleton_iff.mp c.2
    have h2 := congrArg (fun s : ↥H => (s : MulAut Kt)) h1
    rw [hz, hι c]
    exact h2
  obtain ⟨σ, hσdef⟩ : ∃ σ : MulAut Kt, ι n = σ := ⟨_, rfl⟩
  have hodd : Odd (orderOf σ) := by
    have h1 : orderOf σ = orderOf n := by
      rw [← hσdef, hι, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    have h2 : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
    rw [h1]
    exact Nat.coprime_two_left.1 (hNc.coprime_dvd_right h2)
  have hfix : ∀ k : Kt, k * z = z * k → σ k = k := by
    intro k hk
    have hckC : ∀ k : Kt, k * z = z * k → ∃ c : ↥C, ι c = MulAut.conj k := by
      intro k hk
      refine ⟨⟨⟨MulAut.conj k, hH ⟨k, rfl⟩⟩, ?_⟩, ?_⟩
      · rw [hCdef, mem_centralizer_singleton_iff]
        apply Subtype.ext
        show MulAut.conj k * (t : MulAut Kt) = (t : MulAut Kt) * MulAut.conj k
        rw [← hz, ← map_mul, ← map_mul, hk]
      · rw [hι]
    obtain ⟨ck, hck⟩ := hckC k hk
    set N₁ : Subgroup Kt := (N.map ι).comap (MulAut.conj : Kt →* MulAut Kt) with hN₁
    have hN₁z : N₁ ≤ centralizer ({z} : Set Kt) := by
      intro w hw
      have hw' : MulAut.conj w ∈ N.map ι := hw
      obtain ⟨c, -, hcw⟩ := hw'
      have h1 := hιcomm c
      rw [hcw, ← map_mul, ← map_mul] at h1
      exact mem_centralizer_singleton_iff.mpr (hinj h1)
    have hN₁n : (N₁.subgroupOf (centralizer ({z} : Set Kt))).Normal := by
      refine ⟨fun w hw k => ?_⟩
      have hw' : MulAut.conj (w : Kt) ∈ N.map ι := hw
      obtain ⟨c', hc', hc'w⟩ := hw'
      obtain ⟨ck', hck'⟩ := hckC (k : Kt) (mem_centralizer_singleton_iff.mp k.2)
      show MulAut.conj ((k : Kt) * (w : Kt) * (k : Kt)⁻¹) ∈ N.map ι
      refine ⟨ck' * c' * ck'⁻¹, hNn.conj_mem c' hc' ck', ?_⟩
      simp only [map_mul, map_inv, hck', hc'w]
    have hN₁c : Nat.Coprime 2 (Nat.card ↥(N₁.subgroupOf (centralizer ({z} : Set Kt)))) := by
      have h1 : Nat.card ↥(N₁.subgroupOf (centralizer ({z} : Set Kt))) = Nat.card ↥N₁ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₁z).toEquiv
      have h2 : Nat.card ↥N₁ ∣ Nat.card ↥N := by
        have h3 : Nat.card ↥N₁ = Nat.card ↥(N₁.map (MulAut.conj : Kt →* MulAut Kt)) :=
          (Subgroup.card_map_of_injective hinj).symm
        have h4 : N₁.map (MulAut.conj : Kt →* MulAut Kt) ≤ N.map ι := Subgroup.map_comap_le _ _
        have h5 : Nat.card ↥(N.map ι) = Nat.card ↥N := Subgroup.card_map_of_injective hιinj
        rw [h3, ← h5]
        exact Subgroup.card_dvd_of_le h4
      rw [h1]
      exact hNc.coprime_dvd_right h2
    have hle : N₁.subgroupOf (centralizer ({z} : Set Kt)) ≤
        pPrimeCore 2 ↥(centralizer ({z} : Set Kt)) := le_sSup ⟨hN₁n, hN₁c⟩
    rw [hbotz] at hle
    have hm : ι (ck * n * ck⁻¹ * n⁻¹) = MulAut.conj (k * (σ k)⁻¹) := by
      have e1 : ι (ck * n * ck⁻¹ * n⁻¹) = MulAut.conj k * σ * (MulAut.conj k)⁻¹ * σ⁻¹ := by
        simp only [map_mul, map_inv, hck, hσdef]
      rw [e1]
      ext w
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
        MulAut.apply_inv_self]
    have hmem : k * (σ k)⁻¹ ∈ N₁ :=
      ⟨ck * n * ck⁻¹ * n⁻¹, N.mul_mem (hNn.conj_mem n hn ck) (N.inv_mem hn), hm⟩
    have h1 : (⟨k * (σ k)⁻¹, hN₁z hmem⟩ : ↥(centralizer ({z} : Set Kt))) ∈
        N₁.subgroupOf (centralizer ({z} : Set Kt)) := hmem
    have h2 := hle h1
    rw [Subgroup.mem_bot] at h2
    have h3 : k * (σ k)⁻¹ = 1 :=
      congrArg (fun s : ↥(centralizer ({z} : Set Kt)) => (s : Kt)) h2
    exact (mul_inv_eq_one.mp h3).symm
  have hσ1 : σ = 1 := aut_eq_one_of_fixes_centralizer hK hzord hodd hfix
  have h1 : ((n : ↥C) : ↥H) = 1 := Subtype.ext (by rw [← hι n, hσdef]; exact hσ1)
  exact Subtype.ext h1

end Walter

end Ree

end LocBalRee

section Ree


theorem locBal32_ree {Kt : Type} [Group Kt] (hK : QShape4 Kt) (B : Subgroup (MulAut Kt))
    (hB : ∀ b ∈ B, b * b = 1) : IsLocBal32 Kt B := by
  have := LocBalRee.finite_of_qShape4 hK
  exact isLocBal32_of_oddCore (B1.PilotS4.center_of_qShape4 hK)
    (fun _ hH _ ht => LocBalRee.involutionOddCore_eq_bot_ree hK hH ht) B hB

end Ree

end CFSG.GH74.Generic.BProg.B3
