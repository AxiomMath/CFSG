module

public import CFSG.GH74.Generic.BProg.B3.S3T2Loc28
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D1
public import CFSG.GH74.Generic.BProg.B3.Lemma212S45
public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7
public import CFSG.GH74.Generic.BProg.B2.SDUnique

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement MatrixGroups

namespace S3T2

theorem exists_involution_zpowers {X : Type*} [Group X] [Finite X] {g : X}
    (hg : IsPGroup 2 ↥(zpowers g)) (hg1 : g ≠ 1) :
    ∃ τ ∈ zpowers g, τ * τ = 1 ∧ τ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hg.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hg1
    have h1 : Nat.card ↥(zpowers g) = 1 := by rw [hn, pow_zero]
    have hgz : g ∈ zpowers g := Subgroup.mem_zpowers g
    rw [(Subgroup.card_eq_one).1 h1, Subgroup.mem_bot] at hgz
    exact hgz
  have h2 : 2 ∣ Nat.card ↥(zpowers g) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨τ, τ.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one τ
    rw [hτ, pow_two] at this
    exact congrArg Subtype.val this
  · intro h1
    have : τ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hτ
    exact absurd hτ (by norm_num)

theorem card_le_four_of_unique_involution {P : Subgroup (Equiv.Perm (Fin 7))}
    (hP : IsPGroup 2 ↥P) {σ : Equiv.Perm (Fin 7)} (hσ1 : σ ≠ 1)
    (huniq : ∀ τ ∈ P, τ * τ = 1 → τ = 1 ∨ τ = σ) : Nat.card ↥P ≤ 4 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin 7, σ i ≠ i := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  have hstab : ∀ g ∈ P, g i = i → g = 1 := by
    intro g hg hgi
    by_contra hg1
    obtain ⟨τ, hτg, hτ2, hτ1⟩ :=
      exists_involution_zpowers (hP.to_le (Subgroup.zpowers_le.2 hg)) hg1
    have hτi : τ i = i := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hτg
      rw [← hk]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hgi k
    rcases huniq τ (Subgroup.zpowers_le.2 hg hτg) hτ2 with h1 | h1
    · exact hτ1 h1
    · exact hi (h1 ▸ hτi)
  have hinj : Function.Injective (fun g : ↥P => (g : Equiv.Perm (Fin 7)) i) := by
    intro g h hgh
    have h1 : ((h⁻¹ * g : ↥P) : Equiv.Perm (Fin 7)) = 1 := by
      apply hstab _ (h⁻¹ * g).2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
      have hgh' : (g : Equiv.Perm (Fin 7)) i = (h : Equiv.Perm (Fin 7)) i := hgh
      rw [hgh']
      exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
    have h2 : h⁻¹ * g = 1 := Subtype.ext h1
    exact (inv_mul_eq_one.1 h2).symm
  have hle : Nat.card ↥P ≤ 7 := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn] at hle ⊢
  have hn2 : n ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    omega
  calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 4 := by norm_num

theorem card_sl2 (F : Type) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  let := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem eight_dvd_card_sl2 (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    8 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [card_sl2]
  obtain ⟨m, hm⟩ := hodd
  have h1 : Nat.card F ^ 2 - 1 = 4 * (m * (m + 1)) := by
    rw [hm]
    have : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
  rw [h1, hk]
  exact Dvd.intro_left (Nat.card F * k) (by ring)

variable {G : Type} [Group G] [Finite G]

theorem exists_layerHyp' {x : G} {K : Subgroup G} {y : G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hyK : y ∈ K) (hy : orderOf y = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (S : Subgroup ↥(S3.imgBar x K)),
      S3L3Lift.LayerHyp x hK.1 hyK S F := by
  obtain ⟨eK⟩ := B1.PilotS5.hat_equiv_imgBar hK
  have hq3 : QShape3 ↥(S3.imgBar x K) := qShape3_of_mulEquiv eK h3
  have hZt := B1.PilotS3.center_trivial_of_shape3 hK h3
  have hZ : ∀ z : ↥(S3.imgBar x K), (∀ g, g * z = z * g) → z = 1 := by
    intro z hz
    have h1 : eK.symm z = 1 := hZt _ fun g => by
      apply eK.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (eK g)
    simpa using congrArg eK h1
  obtain ⟨F, hF, hFin, S, hodd, h5', e, huS, -, hcomm, hSc, -⟩ :=
    S3L3KGroup.exists_sl2_component hq3 hZ (S3L3Lift.orderOf_yK x hK.1 hyK hy)
  exact ⟨F, hF, hFin, S, ⟨hodd, by omega, e, huS, hSc, fun M hM =>
    S3L3Lift.eq_of_isPCompIn_centralizer hSc hcomm hM⟩⟩

end S3T2

open S3T2

theorem excl_of_mem {G : Type} [Group G] [Finite G] :
    ∀ (x : G) (K A B M : Subgroup G) (a : G) (D J : Subgroup G), Boot15B G x K A B M →
      a ∈ A → Obs32 A a D J → Nonempty ((↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7)) →
        a ∉ K → False := by
  classical
  intro x K A B M a D J h haA hobs hiso haK
  obtain ⟨φ7⟩ := hiso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hILo : IsILo 2 x K := h.term.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hx2 : orderOf x = 2 := hILo.1
  have h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K) := h.shape
  have hsrc : IsSource2 x K A := h.src
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h3
  obtain ⟨E, hEK, hAE, -, hEel, -, -⟩ : ∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧
      x ∉ E ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4 ∧
      (QShape3 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨
        QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) := by
    obtain ⟨-, -, -, hcase⟩ := hsrc
    rcases hcase with ⟨-, h1⟩ | h
    · exact (B1.PilotS3.not_qShape1_of_center_trivial h1 hZ).elim
    · exact h
  obtain ⟨-, hEsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEel
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hEnorm : E ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute x g from
      (Subgroup.mem_centralizer_singleton_iff.mp (hKC (hEK hg))).symm) n).eq
  have haA' : a ∈ ((E ⊔ zpowers x : Subgroup G) : Set G) := by
    rw [← hAE]
    exact haA
  rw [Subgroup.coe_mul_of_left_le_normalizer_right E (zpowers x) hEnorm] at haA'
  obtain ⟨e, heE, y, hy, hey⟩ := haA'
  beta_reduce at hey
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk : x ^ (k % 2) = x ^ k := by
    have := zpow_mod_orderOf x k
    rwa [hx2, Nat.cast_ofNat] at this
  rw [← hk] at hey
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · rw [h0, zpow_zero, mul_one] at hey
    exact haK (hey ▸ hEK heE)
  rw [h0, zpow_one] at hey
  subst hey
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [one_mul] at hobs
    have hJK : J ≠ K := by
      rintro rfl
      have h1 := B2.SD2.SDUnique.lt_card_of_qShape3 h3
      rw [Nat.card_congr φ7.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at h1
      exact absurd h1 (by decide)
    have hKJ := FalseCtxS45Comp.le_cSec_of_ne hobs.comp hK hJK
    have hxJ : x ∈ centralizerSection J (pPrimeCoreOf 2 J) := hobs.y_mem_centralizerSection
    have hAJ : A ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
      rw [hAE]
      exact sup_le (hEK.trans hKJ) (Subgroup.zpowers_le.2 hxJ)
    obtain ⟨hDA, hDel, hDrk⟩ := hobs.D_le
    obtain ⟨d, hdD, hd1⟩ := Th2Sig6.exists_ne_one_of_card (k := pRank 2 ↥D) hDrk
      (C3.Layer1.Back.card_eq_two_pow_pRank hDel)
    exact hobs.D_faith d hdD hd1 (hAJ (hDA hdD))
  have hA3 : pRank 2 ↥A ≤ 3 := by
    obtain ⟨-, hel, hcard, -⟩ := hsrc
    have := hel
    exact (CFSG.pRank_eq_of_card_eq_pow one_lt_two (by simpa using hcard)).le
  have heJ : e ∉ centralizerSection J (pPrimeCoreOf 2 J) := by
    intro hmem
    rcases hobs.cA_eq (isE3_of_isSource2 hsrc) hA3 haA e (hEA heE) hmem with h1 | h1
    · exact he1 h1
    · have hx1 : x = 1 := mul_left_cancel (h1.symm.trans (mul_one e).symm)
      rw [hx1, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
  have heK : e ∈ K := hEK heE
  have he2 : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact hEsq e heE) he1
  obtain ⟨F, hF, hFin, S, hS⟩ := exists_layerHyp' hK h3 heK he2
  obtain ⟨L, hL, -⟩ := hS.exists_comp he2
  have hLeq := hS.pLayerOf_eq he2 hL
  have heL : e ∈ L := by
    rw [← hLeq]
    exact hS.mem_layer he2
  obtain ⟨ψ, hψs, hψk, -⟩ := hS.psi_data he2 hL
  obtain ⟨eS⟩ := hS.equiv
  have hSL := S3Sec29D1.SL2Data.of_equiv eS (S3Sec29D1.sl2Data_sl2 hS.odd)
  have hax : e * x ∈ centralizer ({x} : Set G) :=
    mul_mem (hKC heK) (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hLN : L ≤ normalizer (J : Set G) := by
    have h1 := Lemma212S45.pLayerOf_le_of_balance hx2 hK hax
    rw [Lemma212S45.inf_centralizer_mul_eq (e := e) hKC, hLeq] at h1
    exact h1.trans (Stage1.Thm2.Recip.pLayerOf_le_normalizer hobs.comp)
  set eL : ↥L := ⟨e, heL⟩ with heLdef
  have heL2 : eL * eL = 1 := Subtype.ext (hEsq e heE)
  have heL1 : eL ≠ 1 := fun h1 => he1 (congrArg Subtype.val h1)
  have hker1 : ∀ t : ↥L, t * t = 1 → ψ t = 1 → t = 1 := by
    intro t ht hψt
    have htO : t ∈ pPrimeCore 2 ↥L := by
      rw [← hψk, MonoidHom.mem_ker]
      exact hψt
    exact Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore ht htO
  have hψe : ψ eL = eS.symm (-1) := by
    rcases hSL.invol_eq (ψ eL) (by rw [← map_mul, heL2, map_one]) with h1 | h1
    · exact absurd (hker1 eL heL2 h1) heL1
    · exact h1
  have huniq : ∀ t : ↥L, t * t = 1 → t = 1 ∨ t = eL := by
    intro t ht
    rcases hSL.invol_eq (ψ t) (by rw [← map_mul, ht, map_one]) with h1 | h1
    · exact Or.inl (hker1 t ht h1)
    · right
      have hcomm : t * eL = eL * t :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hL.1 t.2).2)
      have h2 : (t * eL) * (t * eL) = 1 := by
        rw [show (t * eL) * (t * eL) = t * (eL * t) * eL by group, ← hcomm,
          show t * (t * eL) * eL = (t * t) * (eL * eL) by group, ht, heL2, one_mul]
      have h4 := hker1 _ h2 (by rw [map_mul, h1, hψe, hSL.z_sq])
      calc t = t * eL * eL := by rw [mul_assoc, heL2, mul_one]
        _ = eL := by rw [h4, one_mul]
  have h8L : 2 ^ 3 ∣ Nat.card ↥L := by
    have h1 : Nat.card ↥S ∣ Nat.card ↥L := Subgroup.card_dvd_of_surjective hψs
    rw [Nat.card_congr eS.toEquiv] at h1
    exact (eight_dvd_card_sl2 F hS.odd).trans h1
  obtain ⟨H8, hH8⟩ := Sylow.exists_subgroup_card_pow_prime 2 h8L
  have hH8p : IsPGroup 2 ↥H8 := IsPGroup.of_card hH8
  have heH8 : eL ∈ H8 := by
    obtain ⟨h0, hh0, hh01⟩ := Th2Sig6.exists_ne_one_of_card (k := 3) (by norm_num) hH8
    obtain ⟨t, ht, ht2, ht1⟩ :=
      exists_involution_zpowers (hH8p.to_le (Subgroup.zpowers_le.2 hh0)) hh01
    rw [← (huniq t ht2).resolve_left ht1]
    exact Subgroup.zpowers_le.2 hh0 ht
  set ρ : ↥L →* Equiv.Perm (Fin 7) := (Th2.Obs.a7Act J φ7).comp (Subgroup.inclusion hLN)
    with hρ
  have hρe : ρ eL ≠ 1 := by
    intro h1
    apply heJ
    have h2 := (Th2.Obs.a7Act_eq_one_iff φ7 (Subgroup.inclusion hLN eL)).1 h1
    exact (Th2.Obs.barAct_eq_one_iff _).1 h2
  set ρH : ↥H8 →* Equiv.Perm (Fin 7) := ρ.comp H8.subtype with hρH
  have hinj : Function.Injective ρH := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro g hg
    by_contra hg1
    obtain ⟨τ, hτ, hτ2, hτ1⟩ := exists_involution_zpowers (hH8p.to_subgroup _) hg1
    have hτk : ρH τ = 1 := MonoidHom.mem_ker.1 (Subgroup.zpowers_le.2 hg hτ)
    have h1 : (τ : ↥L) = eL :=
      (huniq τ (congrArg Subtype.val hτ2)).resolve_left fun h => hτ1 (Subtype.ext h)
    apply hρe
    rw [← h1]
    exact hτk
  have hPcard : Nat.card ↥ρH.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hH8]
    norm_num
  have hPp : IsPGroup 2 ↥ρH.range := IsPGroup.of_card (n := 3) (by rw [hPcard]; norm_num)
  have hσ1 : ρH ⟨eL, heH8⟩ ≠ 1 := hρe
  have huniqP : ∀ τ ∈ ρH.range, τ * τ = 1 → τ = 1 ∨ τ = ρH ⟨eL, heH8⟩ := by
    rintro _ ⟨g, rfl⟩ hg
    have h2 : g * g = 1 := hinj (by rw [map_mul, hg, map_one])
    rcases huniq g (congrArg Subtype.val h2) with h3 | h3
    · left
      rw [show g = 1 from Subtype.ext h3, map_one]
    · right
      rw [show g = ⟨eL, heH8⟩ from Subtype.ext h3]
  have hle := card_le_four_of_unique_involution hPp hσ1 huniqP
  omega

end CFSG.GH74.Generic.BProg.B3
