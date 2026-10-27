module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113TypeS331
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Hat7

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem stmt5_1_13_type_hat7_of_F4 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h510 : Stmt5_1_10_F4) (hTe : FactType513Three) :
    Stmt5_1_13_type_hat7_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hcl hexp hhat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hHX : H ≤ X := m.inH.1
  have hTX : T ≤ X := hTH.1.trans hHX
  have hTXs : IsSylowTwoOf T X := h.isSylowTwoOf hTX
  have hOT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le hTXs
  have hKX : oTwoUpper H ≤ X := (oTwoUpper_le H).trans hHX
  have hL24 := hc5.1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 m.hyp m.nota
  have heq : K₁ = oTwoUpper H :=
    (m.toEmb512 hk).eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hL24)
  obtain ⟨hst, hnot⟩ := m.star513_F4 h37 h38 h510 heq hcl hL24
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  set Q := modO2Image X Kh₁ with hQ
  set R := modO2Image X (oTwoUpper H) with hR
  set C := Subgroup.centralizer (Q : Set (O2Q X)) with hC
  have hCN : C ≤ Subgroup.normalizer (R : Set (O2Q X)) :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hst.R_le)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hXN : X ≤ Subgroup.normalizer (Kh₁ : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 m.inH.2 hTXs m.hat.1
    rwa [hcl] at this
  have hQN : ∀ g : O2Q X, g ∈ Subgroup.normalizer (Q : Set (O2Q X)) := by
    intro g
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) g
    exact o2Map_mem_normalizer (hXN x'.2)
  have : Q.Normal := ⟨fun q hq g => (Subgroup.mem_normalizer_iff.mp (hQN g) q).mp hq⟩
  obtain ⟨eH⟩ := modO2_mulEquiv m.hat.1
  have hQh : IsHat ↥Q (alternatingGroup (Fin 7)) := IsHat.of_mulEquiv eH hhat
  have hexp' : ∀ d ∈ modO2Image X (D ⊓ X), d ^ 3 ∈ C := hexp
  obtain ⟨-, -, tb, htb, hinv⟩ := hTe (O2Q X) _ _ _ _ _ hst (Or.inr (Or.inl hQh))
    (fun d hd => ⟨1, by rw [pow_one]; exact hexp' d hd⟩) hnot
  obtain ⟨⟨t, htX⟩, ht, rfl⟩ := htb.1
  have htT : t ∈ T := Subgroup.mem_subgroupOf.mp ht
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
  have hbX : b ∈ X := hKX hbK
  set bb := π ⟨b, hbX⟩ with hbbdef
  have hbbR : bb ∈ R := ⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.mpr hbK, rfl⟩
  have hbbQ : bb ∈ Q := hst.R_le hbbR
  have hbbB : bb ∈ modO2Image X B := ⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.mpr hbB, rfl⟩
  have hb3' : (⟨b, hbX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hbb3 : bb ^ 3 = 1 := by
    rw [hbbdef, ← map_pow, hb3', map_one]
  have hbb1 : bb ≠ 1 := by
    intro h1
    apply hb1'
    rw [hbbdef, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h3 := eq_one_of_mem_of_pow_odd (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) h1
      (by decide : Odd 3) hb3'
    exact congrArg Subtype.val h3
  have hbbC : bb ∉ C := by
    intro hbc
    have : IsSimpleGroup (ModO2 R) := isSimpleGroup_of_lieModel_PSL2 hst.R_type
    have : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hst.R_perfect
    have : Group.IsPerfect (ModO2 R) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥R))
    have hZR : Subgroup.center (ModO2 R) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ModO2 R)) with h1 | h1
      · exact h1
      · exact absurd (Subgroup.center_eq_top_iff.mp h1)
          (Group.IsPerfect.not_isMulCommutative (ModO2 R))
    have hbR : (⟨bb, hbbR⟩ : ↥R) ∈ Subgroup.center ↥R := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hbc g (hst.R_le g.2))
    have h1 := Subgroup.map_center_le_center (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥R))
      ⟨_, hbR, rfl⟩
    rw [hZR, Subgroup.mem_bot] at h1
    have h1' := (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥R) (⟨bb, hbbR⟩ : ↥R)).mp h1
    have hbR3 : (⟨bb, hbbR⟩ : ↥R) ^ 3 = 1 := Subtype.ext (by simpa using hbb3)
    have h2 := eq_one_of_mem_of_pow_odd (CFSG.pCore_isPGroup (p := 2) (G := ↥R)) h1'
      (by decide : Odd 3) hbR3
    exact hbb1 (congrArg Subtype.val h2)
  have hcen : ∀ z ∈ Subgroup.center ↥Q, (z : O2Q X) ∈ C := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  obtain ⟨y, hy, hyN⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨⟨d, hdX⟩, hd, rfl⟩ := hy
  have hd' : d ∈ D ⊓ X := Subgroup.mem_subgroupOf.mp hd
  have ho : orderOf d ≠ 0 := (isOfFinOrder_of_finite d).orderOf_pos.ne'
  set s := 3 ^ (orderOf d).factorization 3 with hs
  set r := orderOf d / s with hr
  have hsr : Nat.Coprime s r := Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_three ho)
  have h3r : Nat.Coprime 3 r := Nat.coprime_ordCompl Nat.prime_three ho
  have hsr1 : d ^ (s * r) = 1 := by
    rw [hs, hr, Nat.ordProj_mul_ordCompl_eq_self, pow_orderOf_eq_one]
  have hdb : π ⟨d, hdX⟩ ∈ modO2Image X (D ⊓ X) := ⟨⟨d, hdX⟩, hd, rfl⟩
  have hwC : π ⟨d, hdX⟩ ^ s ∈ C := by
    refine E1.mem_of_pow_mem_of_coprime h3r (hexp' _ ((modO2Image X (D ⊓ X)).pow_mem hdb s)) ?_
    have e : (⟨d, hdX⟩ : ↥X) ^ (s * r) = 1 := Subtype.ext (by simpa using hsr1)
    rw [← pow_mul, ← map_pow, e, map_one]
    exact C.one_mem
  have hclaim : π ⟨d, hdX⟩ ^ r ∈ Subgroup.normalizer (R : Set (O2Q X)) := by
    by_contra hxN
    have hxX : d ^ r ∈ X := X.pow_mem hdX r
    have hxD : d ^ r ∈ D := D.pow_mem hd'.1 r
    have hxb : π ⟨d ^ r, hxX⟩ = π ⟨d, hdX⟩ ^ r := by
      rw [← map_pow]
      rfl
    have hxa : (d ^ r) ^ 3 ^ (orderOf d).factorization 3 = 1 := by
      rw [← pow_mul, mul_comm, ← hs]
      exact hsr1
    have hxbD : π ⟨d ^ r, hxX⟩ ∈ modO2Image X (D ⊓ X) :=
      ⟨⟨d ^ r, hxX⟩, Subgroup.mem_subgroupOf.mpr ⟨hxD, hxX⟩, rfl⟩
    have hxC : π ⟨d ^ r, hxX⟩ ∉ C := fun hc => hxN (hxb ▸ hCN hc)
    have hx3 : (d ^ r) ^ 3 = 1 := h.pow_three_eq_one_of_inv m.nota.2.1 hTX hOT hxD hxX hxa htT
      htb.2 (hexp' _ hxbD) hxC (hinv _ hxbD)
    set xb := π ⟨d ^ r, hxX⟩ with hxbdef
    have hxb3 : xb ^ 3 = 1 := by
      have e : (⟨d ^ r, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [hxbdef, ← map_pow, e, map_one]
    have hbx : bb * xb * bb⁻¹ = xb := by
      refine conj_eq_of_pow_three_of_mem_zpowers hbb3 hxb3 ?_
      have hbN : bb ∈ Subgroup.normalizer (Subgroup.zpowers xb : Set (O2Q X)) :=
        mem_normalizer_of_le_isCyclic hst.D_cyclic (Subgroup.zpowers_le.mpr hxbD)
          (hst.B_le_D hbbB)
      exact (Subgroup.mem_normalizer_iff.mp hbN xb).mp (Subgroup.mem_zpowers xb)
    obtain ⟨φ⟩ := hQh.2.2
    have hodd : Odd (orderOf xb) :=
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hxb3)
    obtain ⟨l, hlQ, hl⟩ := A5.exists_conj_of_odd hQh.1.1 (Or.inr rfl) φ (hQN xb) hodd
    set c := l⁻¹ * xb with hcdef
    have hcC : c ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      calc y * (l⁻¹ * xb) = l⁻¹ * (l * y * l⁻¹) * xb := by group
        _ = l⁻¹ * (xb * y * xb⁻¹) * xb := by rw [hl y hy]
        _ = l⁻¹ * xb * y := by group
    have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hcC l hlQ
    have hxc : xb = l * c := by
      rw [hcdef]
      group
    have hcx : Commute xb c⁻¹ := by
      refine Commute.inv_right ?_
      show xb * c = c * xb
      rw [hxc, ← mul_assoc c l c, ← hlc]
    have hl3 : l ^ 3 ∈ C := by
      have e : l = xb * c⁻¹ := by
        rw [hcdef]
        group
      rw [e, hcx.mul_pow, hxb3, one_mul]
      exact C.pow_mem (C.inv_mem hcC) 3
    have hbl : bb * l = l * bb := by
      have h1 := hl bb hbbQ
      have hxbb : xb * bb = bb * xb := by
        calc xb * bb = bb * xb * bb⁻¹ * bb := by rw [hbx]
          _ = bb * xb := by group
      have h2 : xb * bb * xb⁻¹ = bb := by
        rw [hxbb]
        group
      have h3 : l * bb * l⁻¹ = bb := h1.symm.trans h2
      calc bb * l = l * bb * l⁻¹ * l := by rw [h3]
        _ = l * bb := by group
    have hmem := mem_zpowers_sup_center_of_commute hQh (b := ⟨bb, hbbQ⟩) (l := ⟨l, hlQ⟩)
      (Subtype.ext hbl) (Subtype.ext (by simpa using hbb3))
      (by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (by simpa using Subgroup.mem_centralizer_iff.mp hl3 g g.2))
      (fun hz => hbbC (hcen _ hz))
    have hle : Subgroup.zpowers (⟨bb, hbbQ⟩ : ↥Q) ⊔ Subgroup.center ↥Q ≤
        (Subgroup.normalizer (R : Set (O2Q X))).subgroupOf Q := by
      refine sup_le ?_ fun z hz => ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
        exact Subgroup.le_normalizer hbbR
      · rw [Subgroup.mem_subgroupOf]
        exact hCN (hcen z hz)
    have hlN : l ∈ Subgroup.normalizer (R : Set (O2Q X)) := Subgroup.mem_subgroupOf.mp (hle hmem)
    apply hxN
    rw [← hxb, hxc]
    exact Subgroup.mul_mem _ hlN (hCN hcC)
  exact hyN (E1.mem_of_pow_mem_of_coprime hsr.symm hclaim (hCN hwC))

end CFSG.Quasithin.H13
