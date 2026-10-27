module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.Quasithin.Background.RonanE43Lift
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGTrans
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerMap

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin

variable {K : Type} [Group K] [Finite K] {L V MK : Subgroup K}

theorem eq_bot_of_le_center_of_isCyclic_sylow {E : Type*} [Group E] [Finite E]
    (hE : commutator E = ⊤) (Z : Subgroup E) [Z.Normal] (hZ : Z ≤ Subgroup.center E)
    (hcyc : ∀ r : ℕ, r.Prime → r ∣ Nat.card Z → ∀ S : Sylow r (E ⧸ Z), IsCyclic S) :
    Z = ⊥ := by
  classical
  apply le_antisymm
  · intro z hz
    by_contra hz1
    have hZcard_ne_one : Nat.card Z ≠ 1 := by
      intro hcard
      let : Subsingleton Z := (Nat.card_eq_one_iff_unique.mp hcard).1
      have huniq : ∀ x y : Z, x = y := fun x y => Subsingleton.elim _ _
      apply hz1
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val (huniq ⟨z, hz⟩ 1)
    obtain ⟨r, hrprime, hrdiv⟩ := Nat.exists_prime_and_dvd hZcard_ne_one
    let : Fact r.Prime := ⟨hrprime⟩
    obtain ⟨zZ, hzZorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := Z) r hrdiv
    let zE : E := zZ
    have hzEorder : orderOf zE = r := by
      simpa [zE] using hzZorder
    have hzEcenter : zE ∈ Subgroup.center E := hZ zZ.property
    have hzp : IsPGroup r (Subgroup.zpowers zE) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hzEorder]
      simp
    obtain ⟨S, hzS⟩ := hzp.exists_le_sylow
    let q : E →* E ⧸ Z := QuotientGroup.mk' Z
    let SbarSylow : Sylow r (E ⧸ Z) :=
      Sylow.mapSurjective (QuotientGroup.mk'_surjective Z) S
    let Sbar : Subgroup (E ⧸ Z) := SbarSylow
    have hSbarCyclic : IsCyclic Sbar := hcyc r hrprime hrdiv SbarSylow
    let : IsCyclic Sbar := hSbarCyclic
    let qS : S →* Sbar :=
      ((q.comp (S : Subgroup E).subtype).codRestrict Sbar (by
        intro x
        change q (x : E) ∈ Sbar
        rw [show Sbar = (SbarSylow : Subgroup (E ⧸ Z)) by rfl,
          Sylow.coe_mapSurjective]
        exact Subgroup.mem_map_of_mem q
          (show (x : E) ∈ (S : Subgroup E) from x.property)))
    have hqSker : qS.ker ≤ Subgroup.center S := by
      intro x hx
      apply Subgroup.mem_center_iff.mpr
      intro y
      have hxZ : (x : E) ∈ Z := by
        apply (QuotientGroup.eq_one_iff (x : E)).mp
        exact congrArg Subtype.val hx
      have hxcent : (x : E) ∈ Subgroup.center E := hZ hxZ
      have hxy : (x : E) * (y : E) = (y : E) * (x : E) :=
        (Subgroup.mem_center_iff.mp hxcent (y : E)).symm
      apply Subtype.ext
      exact hxy.symm
    have hcommS : ∀ a b : S, a * b = b * a := by
      intro a b
      exact commutative_of_cyclic_center_quotient qS hqSker a b
    let : IsMulCommutative S := ⟨⟨hcommS⟩⟩
    let : CommGroup S := IsMulCommutative.instCommGroup
    let tr : E →* S := MonoidHom.transfer (MonoidHom.id S)
    have htrivial : ∀ x : E, tr x = 1 := by
      intro x
      have hxcomm : x ∈ commutator E := by
        rw [hE]
        trivial
      have hxker : x ∈ tr.ker :=
        Abelianization.commutator_subset_ker tr hxcomm
      exact hxker
    have hkey : ∀ (k : ℕ) (g₀ : E),
        g₀⁻¹ * zE ^ k * g₀ ∈ (S : Subgroup E) →
          g₀⁻¹ * zE ^ k * g₀ = zE ^ k := by
      intro k g₀ _
      have hzpowcent : zE ^ k ∈ Subgroup.center E :=
        (Subgroup.center E).pow_mem hzEcenter k
      have h := Subgroup.mem_center_iff.mp hzpowcent g₀
      calc
        g₀⁻¹ * zE ^ k * g₀ = g₀⁻¹ * (g₀ * zE ^ k) := by
          rw [mul_assoc, h.symm]
        _ = zE ^ k := by group
    have htransfer_pow :=
      MonoidHom.transfer_eq_pow (MonoidHom.id S) zE hkey
    have hpow_one : zE ^ (S : Subgroup E).index = 1 := by
      have htr := htrivial zE
      rw [htransfer_pow] at htr
      exact congrArg Subtype.val htr
    have hord_dvd_index : r ∣ (S : Subgroup E).index := by
      have h : orderOf zE ∣ (S : Subgroup E).index :=
        (orderOf_dvd_iff_pow_eq_one).2 hpow_one
      simpa [hzEorder] using h
    exact S.not_dvd_index hord_dvd_index
  · exact bot_le

theorem KConf.center_le_MK (h : KConf K L V MK) : Subgroup.center K ≤ MK :=
  (Subgroup.center_le_normalizer (V : Set K)).trans h.kConfig.normalizer_le_MK

theorem KConf.kConfig_bar (h : KConf K L V MK) :
    KConfig (K ⧸ Subgroup.center K) (L.map (QuotientGroup.mk' (Subgroup.center K)))
      (V.map (QuotientGroup.mk' (Subgroup.center K)))
      (MK.map (QuotientGroup.mk' (Subgroup.center K))) := by
  let Z := Subgroup.center K
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  change KConfig (K ⧸ Z) (L.map π) (V.map π) (MK.map π)
  haveI hZnormal : Z.Normal := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hker : π.ker ≤ Subgroup.center K := by rw [hπker]
  have hodd : Nat.Coprime (Nat.card π.ker) 2 := by
    rw [hπker]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      h.odd_card_center.not_two_dvd_nat).symm
  have hVZ : V ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp h.elemAbelian.isPGroup ⟨x, hx.1⟩
    have hxord : orderOf x = 2 ^ n := by
      simpa using (Subgroup.orderOf_coe (⟨x, hx.1⟩ : ↥V)).trans hn
    have hoddx : Odd (orderOf x) :=
      h.odd_card_center.of_dvd_nat (Subgroup.orderOf_dvd_natCard Z hx.2)
    have hpowodd : Odd (2 ^ n) := hxord ▸ hoddx
    have hcop2 : Nat.Coprime (2 ^ n) 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hpowodd.not_two_dvd_nat).symm
    have hcop : Nat.Coprime (orderOf x) (2 ^ n) := by
      rw [hxord]
      exact hcop2.pow_right n
    have hone : orderOf x = 1 :=
      Nat.Coprime.eq_one_of_dvd hcop (by simpa [hxord] using dvd_rfl)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)
  refine
    { ne_bot := ?_
      elemAbelian := h.elemAbelian.map π
      perfect := ?_
      le_normalizer := (Subgroup.map_mono h.le_normalizer).trans (Subgroup.le_normalizer_map π)
      le_pCoreOf := (Subgroup.map_mono h.le_pCoreOf).trans
        (CFSG.LieType.BorelTits.map_pCoreOf_le π L)
      pCoreOf_le := ?_
      eq_commutator := ?_
      le_MK := Subgroup.map_mono h.le_MK
      MK_le_normalizer := (Subgroup.map_mono h.MK_le_normalizer).trans
        (Subgroup.le_normalizer_map π)
      MK_ne_top := ?_
      normalizer_le := ?_ }
  ·
    intro hVbot
    have hVleZ : V ≤ Z := by
      have hVle : V ≤ π.ker := (Subgroup.map_eq_bot_iff V).mp hVbot
      rwa [hπker] at hVle
    have hVbot' : V = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ V ⊓ Z := ⟨hx, hVleZ hx⟩
      have hx1 : x = 1 := by simpa [hVZ] using hx'
      exact Subgroup.mem_bot.mpr hx1
    exact h.ne_bot hVbot'
  ·
    rw [← Subgroup.map_commutator (H₁ := L) (H₂ := L) (f := π), h.perfect]
  ·
    have hPL : pCoreOf 2 (L ⊔ Z) ≤ L := by
      let P : Subgroup K := pCoreOf 2 (L ⊔ Z)
      let A : Subgroup K := L ⊔ Z
      have hPleA : P ≤ A := CFSG.LieType.BorelTits.pCoreOf_le 2 A
      have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A
      have hAnorm : A ≤ Subgroup.normalizer (L : Set K) :=
        sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer (L : Set K))
      haveI hLsubA : (L.subgroupOf A).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hAnorm
      have hPsupA : P ⊔ L ≤ A := sup_le hPleA le_sup_left
      have hpow : ∃ n, L.relIndex P = 2 ^ n := by
        obtain ⟨m, hm⟩ := hP2.exists_card_eq
        obtain ⟨n, -, hn⟩ :=
          (Nat.dvd_prime_pow Nat.prime_two).mp (hm ▸ Subgroup.relIndex_dvd_card L P)
        exact ⟨n, hn⟩
      have hsup_eq : (P.subgroupOf A) ⊔ (L.subgroupOf A) = (P ⊔ L).subgroupOf A :=
        (Subgroup.subgroupOf_sup hPleA le_sup_left).symm
      have hrel1 : L.relIndex (P ⊔ L) = L.relIndex P := by
        rw [← Subgroup.relIndex_subgroupOf (H := L) (K := P ⊔ L) (L := A) hPsupA,
          ← Subgroup.relIndex_subgroupOf (H := L) (K := P) (L := A) hPleA,
          ← hsup_eq]
        exact Subgroup.relIndex_sup_right (P.subgroupOf A) (L.subgroupOf A)
      have hrel2 : L.relIndex (P ⊔ L) ∣ L.relIndex A :=
        ⟨(P ⊔ L).relIndex A,
          (Subgroup.relIndex_mul_relIndex L (P ⊔ L) A le_sup_right hPsupA).symm⟩
      have hsupZ : (Z.subgroupOf A) ⊔ (L.subgroupOf A) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup (le_sup_right : Z ≤ A) (le_sup_left : L ≤ A)]
        rw [show Z ⊔ L = A from sup_comm Z L]
        exact Subgroup.subgroupOf_self A
      have hrel3 : L.relIndex A = L.relIndex Z := by
        calc L.relIndex A = (L.subgroupOf A).relIndex (A.subgroupOf A) :=
              (Subgroup.relIndex_subgroupOf (H := L) (K := A) (L := A) le_rfl).symm
          _ = (L.subgroupOf A).relIndex ⊤ := by rw [Subgroup.subgroupOf_self]
          _ = (L.subgroupOf A).relIndex ((Z.subgroupOf A) ⊔ (L.subgroupOf A)) := by
                rw [hsupZ]
          _ = (L.subgroupOf A).relIndex (Z.subgroupOf A) :=
                Subgroup.relIndex_sup_right (Z.subgroupOf A) (L.subgroupOf A)
          _ = L.relIndex Z :=
                Subgroup.relIndex_subgroupOf (H := L) (K := Z) (L := A) le_sup_right
      have hdvdZ : L.relIndex P ∣ Nat.card Z :=
        (hrel1 ▸ hrel2).trans (hrel3 ▸ Subgroup.relIndex_dvd_card L Z)
      obtain ⟨n, hn⟩ := hpow
      have hoddpow : Odd (2 ^ n) := h.odd_card_center.of_dvd_nat (hn ▸ hdvdZ)
      have hcop : Nat.Coprime (2 ^ n) (2 ^ n) :=
        (((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
          hoddpow.not_two_dvd_nat).symm).pow_right n
      have hpow1 : 2 ^ n = 1 := Nat.Coprime.eq_one_of_dvd hcop dvd_rfl
      exact Subgroup.relIndex_eq_one.mp (by rw [hn, hpow1])
    have hPLcore : pCoreOf 2 (L ⊔ Z) ≤ pCoreOf 2 L :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPL
        ((le_sup_left : L ≤ L ⊔ Z).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ Z)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ Z))
    have hcent : (pCoreOf 2 L).map π ≤
        Subgroup.centralizer (V.map π : Set (K ⧸ Z)) :=
      CFSG.GorensteinWalter.centralizer_map_le_of_hom π V (pCoreOf 2 L) h.pCoreOf_le
    have hpc : pCoreOf 2 (L.map π) = (pCoreOf 2 (L ⊔ Z)).map π := by
      rw [← CFSG.Quasithin.RonanE43.map_pCoreOf_comap_eq π hsurj hker hodd (L.map π)]
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [hpc]
    exact (Subgroup.map_mono hPLcore).trans hcent
  ·
    simpa only [← h.eq_commutator] using Subgroup.map_commutator V L π
  ·
    intro htop
    apply h.MK_ne_top
    have hkerMK : π.ker ≤ MK := by
      rw [hπker]
      exact KConf.center_le_MK h
    calc MK = (MK.map π).comap π := (Subgroup.comap_map_eq_self hkerMK).symm
      _ = (⊤ : Subgroup (K ⧸ Z)).comap π := by rw [htop]
      _ = ⊤ := Subgroup.comap_top π
  ·
    intro Qb hQb_ne hQb_2 hinv
    let Q : Subgroup K := pCoreOf 2 (Qb.comap π)
    have hQb_pcore : pCoreOf 2 Qb = Qb :=
      le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 Qb)
        (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl
          Subgroup.le_normalizer hQb_2)
    have hQmap : Q.map π = Qb := by
      rw [← hQb_pcore]
      exact CFSG.Quasithin.RonanE43.map_pCoreOf_comap_eq π hsurj hker hodd Qb
    have hQ_ne : Q ≠ ⊥ := by
      intro hQbot
      exact hQb_ne (by rw [← hQmap, hQbot, Subgroup.map_bot])
    have hQ_2 : IsPGroup 2 Q :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Qb.comap π)
    have hinvQ : ∀ σ : K ≃* K, V.map σ.toMonoidHom = V → L.map σ.toMonoidHom = L →
        MK.map σ.toMonoidHom = MK → Q.map σ.toMonoidHom = Q := by
      intro σ hV hL hMK
      have hZσ : Z.map σ.toMonoidHom = Z :=
        Subgroup.characteristic_iff_map_eq.mp Subgroup.centerCharacteristic σ
      let σb : (K ⧸ Z) ≃* (K ⧸ Z) := QuotientGroup.congr Z Z σ hZσ
      have happ : ∀ z : K, π (σ z) = σb (π z) := fun z =>
        (QuotientGroup.congr_mk' Z Z σ hZσ z).symm
      have hcomp : σb.toMonoidHom.comp π = π.comp σ.toMonoidHom :=
        MonoidHom.ext fun z => (happ z).symm
      have hVb : (V.map π).map σb.toMonoidHom = V.map π := by
        rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hV]
      have hLb : (L.map π).map σb.toMonoidHom = L.map π := by
        rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hL]
      have hMKb : (MK.map π).map σb.toMonoidHom = MK.map π := by
        rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hMK]
      have hQbσ : Qb.map σb.toMonoidHom = Qb := hinv σb hVb hLb hMKb
      have hstep : ∀ x : K, x ∈ Qb.comap π → σ x ∈ Qb.comap π := by
        intro x hx
        rw [Subgroup.mem_comap] at hx ⊢
        rw [happ x]
        have hmem := Subgroup.mem_map_of_mem σb.toMonoidHom hx
        rwa [hQbσ] at hmem
      have hcomapσ : (Qb.comap π).map σ.toMonoidHom = Qb.comap π := by
        apply le_antisymm
        · exact Subgroup.map_le_iff_le_comap.mpr hstep
        · intro y hy
          rw [Subgroup.mem_comap] at hy
          refine Subgroup.mem_map.mpr ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
          rw [Subgroup.mem_comap]
          have hσbinv : Qb.map σb.symm.toMonoidHom = Qb := by
            have hmap := congrArg (Subgroup.map σb.symm.toMonoidHom) hQbσ
            rw [Subgroup.map_map] at hmap
            have hid : σb.symm.toMonoidHom.comp σb.toMonoidHom = MonoidHom.id _ := by
              ext z
              simp
            rw [hid, Subgroup.map_id] at hmap
            exact hmap.symm
          have hy' : π (σ.symm y) = σb.symm (π y) := by
            apply σb.injective
            rw [MulEquiv.apply_symm_apply]
            rw [← happ (σ.symm y)]
            simp
          rw [hy']
          have hmem := Subgroup.mem_map_of_mem σb.symm.toMonoidHom hy
          rwa [hσbinv] at hmem
      have hQσ : Q.map σ.toMonoidHom = Q := by
        have hmap := CFSG.Quasithin.H13.F431.AG.pCoreOf_map_injective σ.toMonoidHom
          σ.injective (Qb.comap π)
        rw [hcomapσ] at hmap
        exact hmap.symm
      exact hQσ
    have hNQ : Subgroup.normalizer (Q : Set K) ≤ MK :=
      h.normalizer_le Q hQ_ne hQ_2 hinvQ
    intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    have hxN : x ∈ Subgroup.normalizer (Q : Set K) :=
      CFSG.Quasithin.RonanE43.mem_normalizer_of_map_mem π hker hodd hQ_2 (g := x)
        (by rw [hQmap]; exact hy)
    exact Subgroup.mem_map_of_mem π (hNQ hxN)

theorem KConf.inf_center_eq_bot (h : KConf K L V MK)
    (hcyc : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Subgroup.center K) →
      ∀ S : Sylow r (↥(L.map (QuotientGroup.mk' (Subgroup.center K))) ⧸
        CFSG.pCore 2 ↥(L.map (QuotientGroup.mk' (Subgroup.center K)))), IsCyclic S) :
    L ⊓ Subgroup.center K = ⊥ := by
  let Z := Subgroup.center K
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  let Z₀ : Subgroup ↥L := Z.subgroupOf L
  haveI hZnormal : Z.Normal := inferInstance
  haveI : Z₀.Normal := hZnormal.subgroupOf L
  have hE : commutator ↥L = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr h.perfect)
  have hZcenter : Z₀ ≤ Subgroup.center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hx) (y : K)
  have hcyc' : ∀ r : ℕ, r.Prime → r ∣ Nat.card Z₀ →
      ∀ S : Sylow r (↥L ⧸ Z₀), IsCyclic S := by
    intro r hrprime hrdiv S
    let : Fact r.Prime := ⟨hrprime⟩
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := Z₀) r hrdiv
    have hzZ : ((z : ↥L) : K) ∈ Z := Subgroup.mem_subgroupOf.mp z.property
    have hzordL : orderOf (z : ↥L) = r := (Subgroup.orderOf_coe z).trans hzord
    have hzordK : orderOf ((z : ↥L) : K) = r :=
      (Subgroup.orderOf_coe (z : ↥L)).trans hzordL
    have hrZ : r ∣ Nat.card Z := hzordK ▸ Subgroup.orderOf_dvd_natCard Z hzZ
    have hrne2 : r ≠ 2 := by
      intro hr
      exact h.odd_card_center.not_two_dvd_nat (by rwa [hr] at hrZ)
    let Lb : Subgroup (K ⧸ Z) := L.map π
    let φ : ↥L →* ↥Lb :=
      (π.comp L.subtype).codRestrict Lb (fun x => Subgroup.mem_map_of_mem π x.2)
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hkerφ : φ.ker = Z₀ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have h := congrArg (fun y : ↥Lb => (y : K ⧸ Z)) hx
        change ((φ x : ↥Lb) : K ⧸ Z) = 1 at h
        rw [show ((φ x : ↥Lb) : K ⧸ Z) = QuotientGroup.mk' Z (x : K) from rfl] at h
        exact (QuotientGroup.eq_one_iff (x : K)).mp h
      · intro hx
        apply Subtype.ext
        change ((φ x : ↥Lb) : K ⧸ Z) = 1
        rw [show ((φ x : ↥Lb) : K ⧸ Z) = QuotientGroup.mk' Z (x : K) from rfl]
        exact (QuotientGroup.eq_one_iff (x : K)).mpr hx
    let e : (↥L ⧸ Z₀) ≃* ↥Lb :=
      (QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
    let q : ↥Lb →* ↥Lb ⧸ CFSG.pCore 2 ↥Lb := QuotientGroup.mk' (CFSG.pCore 2 ↥Lb)
    have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
    let R : Sylow r ↥Lb := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
    let Sbar : Sylow r (↥Lb ⧸ CFSG.pCore 2 ↥Lb) :=
      Sylow.mapSurjective (f := q) hqsurj R
    have hSbar : IsCyclic Sbar := hcyc r hrprime hrZ Sbar
    have hR2 : IsPGroup r (R : Subgroup ↥Lb) := R.isPGroup'
    have hO2_2 : IsPGroup 2 (CFSG.pCore 2 ↥Lb) :=
      CFSG.LieType.BorelTits.pCore_isPGroup 2
    have hcop : Nat.Coprime (Nat.card (R : Subgroup ↥Lb))
        (Nat.card (CFSG.pCore 2 ↥Lb)) := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR2
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hO2_2
      rw [ha, hb]
      exact Nat.Coprime.pow a b ((Nat.coprime_primes hrprime Nat.prime_two).mpr hrne2)
    have hdisj : (R : Subgroup ↥Lb) ⊓ CFSG.pCore 2 ↥Lb = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    have hInj : Function.Injective (q.subgroupMap (R : Subgroup ↥Lb)) := by
      intro a b hab
      have hq : q ((a : ↥Lb) * (b : ↥Lb)⁻¹) = 1 := by
        have h : q (a : ↥Lb) = q (b : ↥Lb) := congrArg Subtype.val hab
        calc q ((a : ↥Lb) * (b : ↥Lb)⁻¹) = q (a : ↥Lb) * (q (b : ↥Lb))⁻¹ := by
              rw [map_mul, map_inv]
          _ = 1 := by rw [h, mul_inv_cancel]
      have hmemR : (a : ↥Lb) * (b : ↥Lb)⁻¹ ∈ (R : Subgroup ↥Lb) :=
        R.mul_mem a.property (R.inv_mem b.property)
      have hmemO : (a : ↥Lb) * (b : ↥Lb)⁻¹ ∈ CFSG.pCore 2 ↥Lb :=
        (QuotientGroup.eq_one_iff (x := (a : ↥Lb) * (b : ↥Lb)⁻¹)).mp hq
      have hone : (a : ↥Lb) * (b : ↥Lb)⁻¹ = 1 :=
        Subgroup.mem_bot.mp (by rw [← hdisj]; exact ⟨hmemR, hmemO⟩)
      exact Subtype.ext (mul_inv_eq_one.mp hone)
    let eR : (R : Subgroup ↥Lb) ≃* (R : Subgroup ↥Lb).map q :=
      MulEquiv.ofBijective (q.subgroupMap (R : Subgroup ↥Lb))
        ⟨hInj, MonoidHom.subgroupMap_surjective q (R : Subgroup ↥Lb)⟩
    have hRcyc : IsCyclic R := by
      have hRmap : IsCyclic ((R : Subgroup ↥Lb).map q) := by
        rw [← Sylow.coe_mapSurjective (f := q) hqsurj R]
        exact hSbar
      exact eR.isCyclic.mpr hRmap
    have hScyc : IsCyclic S := by
      have hSmap : (S : Subgroup (↥L ⧸ Z₀)).map e.toMonoidHom = (R : Subgroup ↥Lb) :=
        Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
      have hRmap : IsCyclic ((S : Subgroup (↥L ⧸ Z₀)).map e.toMonoidHom) := by
        rw [hSmap]
        exact hRcyc
      exact (e.subgroupMap (S : Subgroup (↥L ⧸ Z₀))).isCyclic.mpr hRmap
    exact hScyc
  have hZ₀bot : Z₀ = ⊥ :=
    eq_bot_of_le_center_of_isCyclic_sylow hE Z₀ hZcenter hcyc'
  have hmap : Z₀.map L.subtype = L ⊓ Z := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨y.property, Subgroup.mem_subgroupOf.mp hy⟩
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.mpr hx.2, rfl⟩
  have hbot : L ⊓ Z = ⊥ := by
    rw [← hmap, hZ₀bot, Subgroup.map_bot]
  exact hbot

end CFSG.SectionRank.QTK.Insp443
