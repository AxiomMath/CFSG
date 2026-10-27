module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113J1ZK

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped MatrixGroups

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem false_of_seven_F4 (h513 : Stmt5_1_3_F4) (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {y : G}
    (hyD : y ∈ D) (hy1 : y ≠ 1) (hy7 : y ^ 7 = 1)
    (hyZ : y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hyB : y ∈ borelL T L := hD.1 hyD
  have hyL : y ∈ L := hyB.1
  have hr : Odd 7 := by decide
  have hn2 : n ≠ 2 := by
    intro hn
    have hcard := (h.isCyclic_card_of_isHall l2TorusFact hD).2
    rw [hn] at hcard
    have h1 := orderOf_dvd_natCard (⟨y, hyD⟩ : ↥D)
    rw [hcard, Subgroup.orderOf_mk] at h1
    have h2 : orderOf y ∣ Nat.gcd 7 (2 ^ 2 - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy7) h1
    rw [show Nat.gcd 7 (2 ^ 2 - 1) = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h2
    exact hy1 h2
  have hred := hV.isTwoReducedIn
  have hVel : IsElemAbelian 2 V := hred.2.2.1
  have hVT : V ≤ T := h.V_le_T hV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hVne : V ≠ ⊥ := fun hb => hV.2.2 (by rw [hb]; exact Subgroup.commutator_bot_left L)
  have hS := h.isSylowTwoOf_inf
  rcases h513 G T M L V n h hV with ⟨W₁, W₂, hL₁, hL₂, hdisj, hsup, hW₁, hW₂⟩ |
    ⟨hn2', -, -⟩ | h3 | h4 | ⟨-, h5', -⟩
  ·
    obtain ⟨z, hzV, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hVel le_rfl hVT hTV hVne
    have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
      hVel.1.is_comm.comm ⟨a, hsup ▸ Subgroup.mem_sup_left ha⟩
        ⟨b, hsup ▸ Subgroup.mem_sup_right hb⟩ |> congrArg Subtype.val
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hzV)
    have hfix : y * (a * b) * y⁻¹ = a * b := by
      rw [← Subgroup.mem_centralizer_iff.mp hyZ (a * b) hzZ, mul_inv_cancel_right]
    have hya : y * a * y⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hL₁ hyL) a).mp ha
    have hyb : y * b * y⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hL₂ hyL) b).mp hb
    have hab := eq_of_mul_eq hdisj hya ha hyb hb (by rw [← hfix]; group)
    by_cases ha1 : a = 1
    · have hb1 : b ≠ 1 := fun hb1 => hz1 (by rw [ha1, hb1, mul_one])
      exact h.conj_ne_of_isNatModCh5_odd hW₂ hyL hr hy7 hy1 hb hb1 hab.2
    · exact h.conj_ne_of_isNatModCh5_odd hW₁ hyL hr hy7 hy1 ha ha1 hab.1
  · exact hn2 hn2'
  ·
    set N := ⁅V, L⁆ with hNdef
    have hNV : N ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
    have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
      le_normalizer_commutator_of hTV h.T_le_normalizer
    obtain ⟨F, _, _, _, -, ψ, Y, hc⟩ := h3.exists_qcoord hS
    have hNL : ⁅N, L⁆ ≠ ⊥ := fun hb =>
      hc.not_le_centralizer (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb))
    have hCL := h.inf_centralizer_le hc.le_normalizer hNL
    have hNne : N ≠ ⊥ := hV.2.2
    obtain ⟨z, hzN, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hVel hNV hVT hTN hNne
    have hzC : z ∉ Subgroup.centralizer (L : Set G) := fun hzC => hz1 (by
      have hmem : z ∈ Z ⊓ Subgroup.centralizer (L : Set G) := ⟨hzZ, hzC⟩
      rwa [hZL, Subgroup.mem_bot] at hmem)
    have hY : Y ⟨z, hzN⟩ ≠ 1 := fun hY => hzC ((hc.ker _).mp hY)
    have hfix : y * z * y⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hyZ z hzZ, mul_inv_cancel_right]
    exact hy1 (hc.eq_one_of_fix_odd hCL hyL hr hy7 hY hfix)
  ·
    obtain ⟨k, hk, -⟩ := id h4
    obtain ⟨z, hzV, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hVel le_rfl hVT hTV hVne
    have hzS : z ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)
        (quasithinOmegaOneCenter_le_inf T hzZ).2
    have hC2 : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) :=
      (pCoreOf_isPGroup 2 L).to_le (h.inf_centralizer_le hLV hV.2.2)
    have hfix : y * z * y⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hyZ z hzZ, mul_inv_cancel_right]
    exact hz1 (IsOrthCh5.eq_one_of_fix_coprime (hk ▸ h4) hS hC2 hyB hr
      (coprime_seven_two_pow_add_one k) hy7 hy1 hzV hzS hfix)
  · exact hn2 (h.n_eq_two_of_isBarS5 hV h5')

end Hyp5_0_1

namespace Main513

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem exists_seven_F4 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h510 : Stmt5_1_10_F4)
    (m : Main513 G T M L V H B D K₁ X Kh₁ n) (hc5 : Case5_512 T H X Kh₁)
    (hcl : conjClosure Kh₁ T = Kh₁) (hJ : IsSporadic .J1 ↥(o2Img X Kh₁))
    (h7 : ∀ d ∈ o2Img X (D ⊓ X),
      d ^ 7 ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X)))
    (hn3 : ¬ ∀ d ∈ o2Img X (D ⊓ X), ∃ k : ℕ,
      d ^ (3 ^ k) ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X))) :
    ∃ y ∈ D, y ∈ Kh₁ ∧ y ≠ 1 ∧ y ^ 7 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hHX : H ≤ X := m.inH.1
  have hTX : T ≤ X := hTH.1.trans hHX
  have hTXs : IsSylowTwoOf T X := h.isSylowTwoOf hTX
  have hKX : oTwoUpper H ≤ X := (oTwoUpper_le H).trans hHX
  have hKKh : oTwoUpper H ≤ Kh₁ := m.lt.le.trans hcl.le
  have hXN : X ≤ Subgroup.normalizer (Kh₁ : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 m.inH.2 hTXs m.hat.1
    rwa [hcl] at this
  obtain ⟨-, -, hBorel, hHall, -⟩ := h510 G T M L H B D n m.hyp m.nota
  rw [m.hyp.borel_eq hBorel] at hHall
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hB3 : Nat.card B = 3 := by
    have := (isCyclic_card_of_isHall_borelOf le_rfl hc5.1 hTK hHall).2
    norm_num at this
    exact this
  have hBne : B ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hB3
    omega
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  have hb3 : b ^ 3 = 1 := by
    have := orderOf_dvd_natCard (⟨b, hbB⟩ : ↥B)
    rw [hB3, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hbK : b ∈ oTwoUpper H := (hHall.1 hbB).1
  have hbKh : b ∈ Kh₁ := hKKh hbK
  have hbX : b ∈ X := hKX hbK
  have hbD : b ∈ Subgroup.normalizer (D : Set G) := m.nota.2.2 hbB
  push Not at hn3
  obtain ⟨xb, hxb, hk⟩ := hn3
  obtain ⟨⟨x, hxX⟩, hxDX, rfl⟩ := Subgroup.mem_map.mp hxb
  have hxD : x ∈ D := (Subgroup.mem_subgroupOf.mp hxDX).1
  set xb := QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨x, hxX⟩ : ↥X) with hxbdef
  set Q := o2Img X Kh₁ with hQ
  have hQN : ∀ g : O2Q X, g ∈ Subgroup.normalizer (Q : Set (O2Q X)) := by
    intro g
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) g
    exact o2Map_mem_normalizer (hXN x'.2)
  have : Q.Normal := ⟨fun k hk g => (Subgroup.mem_normalizer_iff.mp (hQN g) k).mp hk⟩
  obtain ⟨e⟩ := hJ
  obtain ⟨q, hq⟩ := exists_eq_conj_of_j1 e (MulAut.conjNormal xb)
  have hqk : ∀ k : ↥Q, xb * (k : O2Q X) * xb⁻¹ = ((q * k * q⁻¹ : ↥Q) : O2Q X) := by
    intro k
    rw [← MulAut.conjNormal_apply, hq, MulAut.conj_apply]
  have hq1 : q ≠ 1 := by
    intro hq1
    apply hk 0
    rw [pow_zero, pow_one, Subgroup.mem_centralizer_iff]
    intro k hkQ
    have h1 := hqk ⟨k, hkQ⟩
    simp only [hq1, one_mul, inv_one, mul_one] at h1
    calc k * xb = xb * k * xb⁻¹ * xb := by rw [h1]
      _ = xb * k := by group
  have hq7 : q ^ 7 = 1 := by
    have hc7 : MulAut.conj (q ^ 7) = 1 := by
      rw [map_pow, ← hq, ← map_pow]
      ext k
      have hc := Subgroup.mem_centralizer_iff.mp (h7 xb hxb) k k.2
      rw [MulAut.conjNormal_apply, MulAut.one_apply, ← hc, mul_inv_cancel_right]
    apply eq_one_of_forall_commute_of_j1 e
    intro k
    have h1 := congrArg (fun f : MulAut ↥Q => f k) hc7
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc q ^ 7 * k = q ^ 7 * k * (q ^ 7)⁻¹ * q ^ 7 := by group
      _ = k * q ^ 7 := by rw [h1]
  have hq30 : Nat.Coprime (orderOf q) 30 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hq7) (by norm_num)
  set bb := QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨b, hbX⟩ : ↥X) with hbbdef
  have hbbQ : bb ∈ Q := ⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.mpr hbKh, rfl⟩
  have hb3' : (⟨b, hbX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hbb3 : orderOf (⟨bb, hbbQ⟩ : ↥Q) = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show bb ^ 3 = 1
      rw [hbbdef, ← map_pow, hb3', map_one]
    · intro h1
      apply hb1'
      have h2 : bb = 1 := congrArg Subtype.val h1
      rw [hbbdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have h3 := eq_one_of_mem_of_pow_odd (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) h2
        (by decide : Odd 3) hb3'
      exact congrArg Subtype.val h3
  have hyD : x * b * x⁻¹ * b⁻¹ ∈ D := by
    have h1 : b * x⁻¹ * b⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hbD x⁻¹).mp (D.inv_mem hxD)
    rw [show x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) by group]
    exact D.mul_mem hxD h1
  have hyKh : x * b * x⁻¹ * b⁻¹ ∈ Kh₁ :=
    Kh₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXN hxX) b).mp hbKh) (Kh₁.inv_mem hbKh)
  have hyX : x * b * x⁻¹ * b⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem (X.mul_mem hxX hbX) (X.inv_mem hxX)) (X.inv_mem hbX)
  refine ⟨x * b * x⁻¹ * b⁻¹, hyD, hyKh, ?_, ?_⟩
  ·
    intro h1
    have hxbx : x * b * x⁻¹ = b := by
      calc x * b * x⁻¹ = x * b * x⁻¹ * b⁻¹ * b := by group
        _ = b := by rw [h1, one_mul]
    have h2 : xb * bb * xb⁻¹ = bb := by
      have h3 : (⟨x, hxX⟩ * ⟨b, hbX⟩ * (⟨x, hxX⟩ : ↥X)⁻¹ : ↥X) = ⟨b, hbX⟩ := Subtype.ext hxbx
      rw [hxbdef, hbbdef, ← map_inv, ← map_mul, ← map_mul, h3]
    have h3 := hqk ⟨bb, hbbQ⟩
    rw [h2] at h3
    have h4 : (⟨bb, hbbQ⟩ : ↥Q) = q * ⟨bb, hbbQ⟩ * q⁻¹ := Subtype.ext h3
    have hcomm : q * ⟨bb, hbbQ⟩ = ⟨bb, hbbQ⟩ * q := by
      calc q * ⟨bb, hbbQ⟩ = q * ⟨bb, hbbQ⟩ * q⁻¹ * q := by group
        _ = ⟨bb, hbbQ⟩ * q := by rw [← h4]
    exact hq1 (eq_one_of_commute_of_j1 e hq30 hbb3 hcomm)
  ·
    set y := x * b * x⁻¹ * b⁻¹ with hydef
    set yb := QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨y, hyX⟩ : ↥X) with hybdef
    have hybD : yb ∈ o2Img X (D ⊓ X) :=
      ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.mpr ⟨hyD, hyX⟩, rfl⟩
    have hybQ : yb ∈ Q := ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.mpr hyKh, rfl⟩
    have hyb7 : yb ^ 7 = 1 := by
      have h1 := eq_one_of_forall_commute_of_j1 e (z := ⟨yb ^ 7, Q.pow_mem hybQ 7⟩)
        (fun k => Subtype.ext ((Subgroup.mem_centralizer_iff.mp (h7 yb hybD) k k.2).symm))
      exact congrArg Subtype.val h1
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ((⟨y, hyX⟩ : ↥X) ^ 7) = 1 := by
      rw [map_pow]
      exact hyb7
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hP : IsPGroup 2 ↥((CFSG.pCore 2 ↥X).map X.subtype) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map _
    have hmem : y ^ 7 ∈ (CFSG.pCore 2 ↥X).map X.subtype := ⟨_, h2, by simp⟩
    exact eq_one_of_mem_of_mem_odd hP m.nota.2.1.2.1 hmem (D.pow_mem hyD 7)

end Main513

end CFSG.Quasithin.H13
