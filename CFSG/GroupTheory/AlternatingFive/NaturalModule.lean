module

public import CFSG.GroupTheory.AlternatingFive.SmallImage

public section

namespace CFSG.GroupTheory.AlternatingFive

open CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

private abbrev ModV (Q W : Subgroup G) : Type _ := ↥Q ⧸ W.subgroupOf Q

private structure ModVSetup (L Q W : Subgroup G) where
  smul : MulDistribMulAction ↥L ↥Q
  qfin : Finite ↥Q
  wnormal : (W.subgroupOf Q).Normal
  comm : IsMulCommutative (ModV Q W)

private def modVSetup {L Q W : Subgroup G} [Finite ↥L] (hQL : Q ≤ L)
    (hQn : L ≤ Subgroup.normalizer (Q : Set G))
    (hWQ : W ≤ Q) (hWn : L ≤ Subgroup.normalizer (W : Set G))
    (hQW : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ W) : ModVSetup L Q W where
  smul := MulDistribMulAction.compHom ↥Q
    ((Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hQn))
  qfin := Finite.of_injective (Subgroup.inclusion hQL) (Subgroup.inclusion_injective hQL)
  wnormal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWQ).mpr (hQL.trans hWn)
  comm := by
    letI : (W.subgroupOf Q).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWQ).mpr (hQL.trans hWn)
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf]
    exact hQW a a.2 b b.2

private theorem modV_sigma_smul
    {L Q W : Subgroup G} [Finite ↥L] [MulDistribMulAction ↥L ↥Q]
    {c : G} {φ : MulAut ↥Q}
    (hφ_coe : ∀ q : ↥Q, ((φ q : ↥Q) : G) = c * (q : G) * c⁻¹)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hQn : L ≤ Subgroup.normalizer (Q : Set G))
    (hQW : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ W)
    (hcLQ : ∀ l ∈ L, ⁅c, l⁆ ∈ Q)
    [hWnormal : (W.subgroupOf Q).Normal]
    (hsmul : ∀ (l : ↥L) (q : ↥Q),
      ((l • q : ↥Q) : G) = (l : G) * (q : G) * (l : G)⁻¹)
    [MulAction ↥L (ModV Q W)]
    (hsmul_mk : ∀ (l : ↥L) (q : ↥Q),
      l • (QuotientGroup.mk q : ModV Q W) = QuotientGroup.mk (l • q))
    (σ : ModV Q W ≃* ModV Q W)
    (hσ_mk : ∀ q : ↥Q, σ (QuotientGroup.mk q) = QuotientGroup.mk (φ q)) :
    ∀ (l : ↥L) (v : ModV Q W), σ (l • v) = l • σ v := by
  intro l v
  refine QuotientGroup.induction_on v ?_
  intro q
  rw [hsmul_mk, hσ_mk, hσ_mk, hsmul_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  rw [Subgroup.mem_subgroupOf]
  let u : G := ⁅c, (l : G)⁆⁻¹
  have hlc : (l : G) * c * (l : G)⁻¹ = u * c := by
    dsimp [u]
    rw [commutatorElement_def]
    group
  have hD : (l : G) * (c * (q : G) * c⁻¹) * (l : G)⁻¹ =
      u * (c * ((l : G) * (q : G) * (l : G)⁻¹) * c⁻¹) * u⁻¹ := by
    calc (l : G) * (c * (q : G) * c⁻¹) * (l : G)⁻¹
        = ((l : G) * c * (l : G)⁻¹) * ((l : G) * (q : G) * (l : G)⁻¹) *
            ((l : G) * c * (l : G)⁻¹)⁻¹ := by group
      _ = u * (c * ((l : G) * (q : G) * (l : G)⁻¹) * c⁻¹) * u⁻¹ := by
            rw [hlc]
            group
  have hxQ : c * ((l : G) * (q : G) * (l : G)⁻¹) * c⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hcQ _).mp
      ((Subgroup.mem_normalizer_iff.mp (hQn l.2) (q : G)).mp q.2)
  have huQ : u ∈ Q := by
    dsimp [u]
    exact Q.inv_mem (hcLQ l l.2)
  have hcommW : ⁅c * ((l : G) * (q : G) * (l : G)⁻¹) * c⁻¹, u⁆ ∈ W :=
    hQW _ hxQ _ huQ
  have hcoe : (((φ (l • q) : ↥Q) / (l • φ q) : ↥Q) : G) =
      (c * ((l : G) * (q : G) * (l : G)⁻¹) * c⁻¹) /
        ((l : G) * (c * (q : G) * c⁻¹) * (l : G)⁻¹) := by
    rw [Subgroup.coe_div, hφ_coe, hsmul, hsmul, hφ_coe]
  rw [hcoe, hD]
  have hratio :
      (c * ((l : G) * (q : G) * (l : G)⁻¹) * c⁻¹) /
        (u * (c * ((l : G) * (q : G) * (l : G)⁻¹) * c⁻¹) * u⁻¹) =
      ⁅c * ((l : G) * (q : G) * (l : G)⁻¹) * c⁻¹, u⁆ := by
    rw [div_eq_mul_inv, commutatorElement_def]
    group
  rw [hratio]
  exact hcommW

private theorem modV_fbar_exists
    {L Q W : Subgroup G} [Finite ↥L] [hWnormal : (W.subgroupOf Q).Normal]
    [MulDistribMulAction ↥L ↥Q]
    [IsMulCommutative (ModV Q W)] [MulAction ↥L (ModV Q W)]
    {φ : MulAut ↥Q}
    (hsmul_mk : ∀ (l : ↥L) (q : ↥Q),
      l • (QuotientGroup.mk q : ModV Q W) = QuotientGroup.mk (l • q))
    (σ : ModV Q W ≃* ModV Q W)
    (hσ_mk : ∀ q : ↥Q, σ (QuotientGroup.mk q) = QuotientGroup.mk (φ q))
    (hσ_smul : ∀ (l : ↥L) (v : ModV Q W), σ (l • v) = l • σ v) :
    ∃ fbar : ModV Q W →* ModV Q W,
      (∀ q : ↥Q, fbar (QuotientGroup.mk q) =
        QuotientGroup.mk (φ q * q⁻¹)) ∧
      ∀ (l : ↥L) (v : ModV Q W), fbar (l • v) = l • fbar v := by
  let fbar : ModV Q W →* ModV Q W :=
  { toFun := fun v => σ v * v⁻¹
    map_one' := by simp
    map_mul' := fun a b => by
      change σ (a * b) * (a * b)⁻¹ = (σ a * a⁻¹) * (σ b * b⁻¹)
      rw [map_mul]
      simp only [mul_inv_rev]
      ac_rfl }
  have hfbar_mk : ∀ q : ↥Q, fbar (QuotientGroup.mk q) =
      QuotientGroup.mk (φ q * q⁻¹) := by
    intro q
    change σ (QuotientGroup.mk q) * (QuotientGroup.mk q)⁻¹ =
      QuotientGroup.mk (φ q * q⁻¹)
    rw [hσ_mk]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hfbar_smul : ∀ (l : ↥L) (v : ModV Q W), fbar (l • v) = l • fbar v := by
    intro l v
    refine QuotientGroup.induction_on v ?_
    intro q
    change fbar (l • QuotientGroup.mk q) = l • fbar (QuotientGroup.mk q)
    rw [hsmul_mk, hfbar_mk, hfbar_mk, hsmul_mk, smul_mul', smul_inv']
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    have h1 : (QuotientGroup.mk (s := W.subgroupOf Q) (φ (l • q)) : ModV Q W) =
        QuotientGroup.mk (s := W.subgroupOf Q) (l • φ q) := by
      have h := hσ_smul l (QuotientGroup.mk (s := W.subgroupOf Q) q : ModV Q W)
      rw [hsmul_mk l q, hσ_mk, hσ_mk, hsmul_mk l (φ q)] at h
      exact h
    rw [h1]
  exact ⟨fbar, hfbar_mk, hfbar_smul⟩

private theorem modV_ker_ne_bot
    {L Q W : Subgroup G} [Finite ↥L] [hWnormal : (W.subgroupOf Q).Normal]
    [Finite (ModV Q W)] [IsMulCommutative (ModV Q W)] [MulAction ↥L (ModV Q W)]
    {φ : MulAut ↥Q} {σ : Equiv.Perm (ModV Q W)} {m : ℕ}
    (hσ_mk : ∀ q : ↥Q, σ (QuotientGroup.mk q) = QuotientGroup.mk (φ q))
    (hσ_one : σ (1 : ModV Q W) = 1)
    (hσpow : σ ^ (2 ^ m) = 1)
    (hcard : Nat.card (ModV Q W) = 16)
    (fbar : ModV Q W →* ModV Q W)
    (hfbar_mk : ∀ q : ↥Q, fbar (QuotientGroup.mk q) =
      QuotientGroup.mk (φ q * q⁻¹)) :
    fbar.ker ≠ ⊥ := by
  haveI : Fintype (ModV Q W) := Fintype.ofFinite (ModV Q W)
  have hVcard : Fintype.card (ModV Q W) = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨b, hbfix, hbne⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime' (p := 2) (n := m)
      (by rw [hVcard]; norm_num) hσpow hσ_one
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective b
  have hqnotW : q ∉ W.subgroupOf Q := by
    intro hq
    apply hbne
    exact (QuotientGroup.eq_one_iff (N := W.subgroupOf Q) (x := q)).mpr hq
  intro hbot
  have hqker : QuotientGroup.mk q ∈ fbar.ker := by
    rw [MonoidHom.mem_ker, hfbar_mk]
    have hfix : (QuotientGroup.mk (s := W.subgroupOf Q) (φ q) : ModV Q W) =
        QuotientGroup.mk (s := W.subgroupOf Q) q := by
      rw [← hσ_mk q]
      exact hbfix
    have hdiv : (φ q) / q ∈ W.subgroupOf Q :=
      QuotientGroup.eq_iff_div_mem.mp hfix
    rw [Subgroup.mem_subgroupOf] at hdiv
    have hmem : (φ q * q⁻¹ : ↥Q) ∈ W.subgroupOf Q := by
      rw [Subgroup.mem_subgroupOf]
      simpa [Subgroup.coe_div, div_eq_mul_inv] using hdiv
    exact (QuotientGroup.eq_one_iff (N := W.subgroupOf Q) (x := φ q * q⁻¹)).mpr hmem
  have : QuotientGroup.mk q ∈ (⊥ : Subgroup (ModV Q W)) := by
    rw [← hbot]
    exact hqker
  rw [Subgroup.mem_bot] at this
  exact hqnotW ((QuotientGroup.eq_one_iff (N := W.subgroupOf Q) (x := q)).mp this)

private theorem modV_free_of_fixed
    {L Q W : Subgroup G} [Finite ↥L] [hWnormal : (W.subgroupOf Q).Normal]
    [MulDistribMulAction ↥L ↥Q] [MulAction ↥L (ModV Q W)]
    (hQL : Q ≤ L) (hWn : L ≤ Subgroup.normalizer (W : Set G))
    (hfpf : ∀ x ∈ L, orderOf x = 3 → ∀ q ∈ Q, ⁅q, x⁆ ∈ W → q ∈ W)
    (hsmul : ∀ (l : ↥L) (q : ↥Q),
      ((l • q : ↥Q) : G) = (l : G) * (q : G) * (l : G)⁻¹)
    (hsmul_mk : ∀ (l : ↥L) (q : ↥Q),
      l • (QuotientGroup.mk q : ModV Q W) = QuotientGroup.mk (l • q))
    {x : ↥L} (hx3 : orderOf x = 3)
    (R : Subgroup (ModV Q W)) [MulAction ↥L ↥R]
    (hsmulR : ∀ (l : ↥L) (r : ↥R),
      ((l • r : ↥R) : ModV Q W) = l • (r : ModV Q W)) :
    ∀ r : ↥R, x • r = r → r = 1 := by
  have hxG3 : orderOf (x : G) = 3 := by
    rw [Subgroup.orderOf_coe, hx3]
  intro r hr
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (r : ModV Q W)
  have hr' : x • (QuotientGroup.mk q : ModV Q W) = QuotientGroup.mk q := by
    rw [hq, ← hsmulR x r]
    exact congrArg Subtype.val hr
  rw [hsmul_mk] at hr'
  have hdiv : ((((x : ↥L) • q : ↥Q) : G) / (q : G)) ∈ W := by
    have h := QuotientGroup.eq_iff_div_mem.mp hr'
    rw [Subgroup.mem_subgroupOf] at h
    simpa [Subgroup.coe_div] using h
  rw [hsmul x q, div_eq_mul_inv] at hdiv
  have hqinvW : (q : G)⁻¹ ∈ W := by
    have hcomm : ⁅(q : G)⁻¹, (x : G)⁆ ∈ W := by
      rw [commutatorElement_def]
      rw [show (q : G)⁻¹ * (x : G) * (q : G)⁻¹⁻¹ * (x : G)⁻¹ =
          (q : G)⁻¹ * (((x : G) * (q : G) * (x : G)⁻¹) * (q : G)⁻¹) * (q : G) by
        group]
      have hconj := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem (Subgroup.normalizer (W : Set G)) (hWn (hQL q.2))) _).mp hdiv
      simpa only [inv_inv] using hconj
    exact (hfpf (x : G) x.2 hxG3) (q : G)⁻¹ (Q.inv_mem q.2) hcomm
  have hqW : q ∈ W.subgroupOf Q := by
    rw [Subgroup.mem_subgroupOf]
    simpa using W.inv_mem hqinvW
  have hone : QuotientGroup.mk q = (1 : ModV Q W) :=
    (QuotientGroup.eq_one_iff (N := W.subgroupOf Q) (x := q)).mpr hqW
  apply Subtype.ext
  rw [← hq]
  exact hone

private theorem modV_card_range_modEq_one
    {L V : Type} [Group L] [Finite L] [Group V] [Finite V] [MulAction L V]
    (R : Subgroup V) [MulAction L ↥R]
    (hsmulR : ∀ (l : L) (r : ↥R), ((l • r : ↥R) : V) = l • (r : V))
    (hone : ∀ l : L, l • (1 : V) = 1)
    {x : L} (hx3pow : x ^ 3 = 1)
    (hfree : ∀ r : ↥R, x • r = r → r = 1) :
    Nat.card R ≡ 1 [MOD 3] := by
  classical
  haveI : Fintype ↥R := Fintype.ofFinite ↥R
  let σR : Equiv.Perm ↥R := MulAction.toPermHom L ↥R x
  have hσR3 : σR ^ 3 = 1 := by
    rw [show σR = MulAction.toPermHom L ↥R x from rfl, ← map_pow, hx3pow, map_one]
  have hsupp : σR.supportᶜ = ({1} : Finset ↥R) := by
    ext r
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, Finset.mem_singleton]
    constructor
    · intro hr
      have hxr : x • r = r := by
        simpa [σR] using hr
      exact hfree r hxr
    · intro hr
      subst hr
      have h1 : σR 1 = 1 := by
        change (x • (1 : ↥R) : ↥R) = 1
        apply Subtype.ext
        rw [hsmulR x 1]
        exact hone x
      rw [h1]
      simp
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) hσR3
  rw [hsupp] at hmod
  simpa [Nat.card_eq_fintype_card] using hmod.symm

private theorem modV_range_eq_bot
    {L V : Type} [Group L] [Finite L] [Group V] [Finite V] [MulAction L V]
    (R : Subgroup V) [MulAction L ↥R]
    {x : L} (hmodR : Nat.card R ≡ 1 [MOD 3])
    (hfree : ∀ r : ↥R, x • r = r → r = 1)
    (hRdvd : Nat.card R ∣ 16) (hRlt : Nat.card R < 16)
    (hx3 : orderOf x = 3)
    (e : oTwoQuot L ≃* alternatingGroup (Fin 5)) :
    R = ⊥ := by
  by_contra hRne_bot
  have hRgt1 : 1 < Nat.card R := (Subgroup.one_lt_card_iff_ne_bot R).mpr hRne_bot
  have hR4 : Nat.card R = 4 := by
    have hle8 : Nat.card R ≤ 8 := by
      have hdvd' : Nat.card R ∣ 2 ^ 4 := by norm_num at hRdvd ⊢; exact hRdvd
      obtain ⟨j, hj4, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
      have hjlt : j < 4 := by
        by_contra hge
        have h4le : 4 ≤ j := by omega
        have hpow : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h4le
        rw [hj] at hRlt
        omega
      have hj3 : j ≤ 3 := by omega
      calc Nat.card R = 2 ^ j := hj
        _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj3
        _ = 8 := by norm_num
    set n := Nat.card R with hn
    have hnle : n ≤ 8 := by rw [hn]; exact hle8
    have hn0 : n ≠ 0 := by intro h; rw [h] at hRgt1; norm_num at hRgt1
    have hn1 : n ≠ 1 := by intro h; rw [h] at hRgt1; norm_num at hRgt1
    have hn2 : n ≠ 2 := by intro h; rw [h] at hmodR; norm_num at hmodR
    have hn3 : n ≠ 3 := by intro h; rw [h] at hRdvd; norm_num at hRdvd
    have hn5 : n ≠ 5 := by intro h; rw [h] at hRdvd; norm_num at hRdvd
    have hn6 : n ≠ 6 := by intro h; rw [h] at hRdvd; norm_num at hRdvd
    have hn7 : n ≠ 7 := by intro h; rw [h] at hRdvd; norm_num at hRdvd
    have hn8 : n ≠ 8 := by intro h; rw [h] at hmodR; norm_num at hmodR
    omega
  have hPermcard : Nat.card (Equiv.Perm ↥R) < 60 := by
    rw [Nat.card_perm, hR4]
    norm_num
  have hxkill : MulAction.toPermHom L ↥R x = 1 :=
    CFSG.GroupTheory.AlternatingFive.map_eq_one_of_orderOf_eq_three_of_card_lt_sixty
      (L := L) (H := Equiv.Perm ↥R) e (MulAction.toPermHom L ↥R) hPermcard hx3
  haveI : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne_bot
  obtain ⟨r, hrne⟩ := exists_ne (1 : ↥R)
  have hfix : x • r = r := by
    have := congrArg (fun f : Equiv.Perm ↥R => f r) hxkill
    simpa using this
  exact hrne (hfree r hfix)

private theorem modV_sigma_exists
    {L Q W : Subgroup G} [Finite ↥L] [hWnormal : (W.subgroupOf Q).Normal]
    {c : G} (m : ℕ) (hm : c ^ (2 ^ m) = 1)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hcW : c ∈ Subgroup.normalizer (W : Set G))
    (hWQ : W ≤ Q) (hWn : L ≤ Subgroup.normalizer (W : Set G)) :
    ∃ (φ : MulAut ↥Q) (σe : ModV Q W ≃* ModV Q W),
      (∀ q : ↥Q, ((φ q : ↥Q) : G) = c * (q : G) * c⁻¹) ∧
      (∀ q : ↥Q, σe (QuotientGroup.mk q) = QuotientGroup.mk (φ q)) ∧
      (σe.toEquiv ^ (2 ^ m) = 1) := by
  let φ : MulAut ↥Q := (Subgroup.normalizerMonoidHom Q) ⟨c, hcQ⟩
  have hφ_coe : ∀ q : ↥Q, ((φ q : ↥Q) : G) = c * (q : G) * c⁻¹ := by
    intro q
    exact Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨c, hcQ⟩ q
  let cInv : Subgroup.normalizer (Q : Set G) :=
    ⟨c⁻¹, Subgroup.inv_mem (Subgroup.normalizer (Q : Set G)) hcQ⟩
  have hφinv : φ⁻¹ = (Subgroup.normalizerMonoidHom Q) cInv := by
    dsimp [φ]
    rw [← map_inv]
    congr
  have hφsymm_coe : ∀ q : ↥Q, ((φ.symm q : ↥Q) : G) = c⁻¹ * (q : G) * c := by
    intro q
    rw [show φ.symm = (Subgroup.normalizerMonoidHom Q) cInv from hφinv]
    simpa [cInv] using Subgroup.normalizerMonoidHom_apply_apply_coe Q cInv q
  have hmapW : (W.subgroupOf Q).map φ.toMonoidHom = W.subgroupOf Q := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (y : G) ∈ W at hy
      change ((φ y : ↥Q) : G) ∈ W
      rw [hφ_coe y]
      exact (Subgroup.mem_normalizer_iff.mp hcW (y : G)).mp hy
    · intro hx
      change (x : G) ∈ W at hx
      refine ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
      change ((φ.symm x : ↥Q) : G) ∈ W
      rw [hφsymm_coe x]
      have hcInvW : c⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
        Subgroup.inv_mem (Subgroup.normalizer (W : Set G)) hcW
      simpa using (Subgroup.mem_normalizer_iff.mp hcInvW (x : G)).mp hx
  let σe : ModV Q W ≃* ModV Q W :=
    QuotientGroup.congr (W.subgroupOf Q) (W.subgroupOf Q) φ hmapW
  have hσ_mk : ∀ q : ↥Q, σe (QuotientGroup.mk q) = QuotientGroup.mk (φ q) := by
    intro q
    exact QuotientGroup.congr_mk (W.subgroupOf Q) (W.subgroupOf Q) φ hmapW q
  have hφpow : φ ^ (2 ^ m) = 1 := by
    have hcNpow : (⟨c, hcQ⟩ : Subgroup.normalizer (Q : Set G)) ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      simpa using hm
    dsimp [φ]
    rw [← map_pow, hcNpow, map_one]
  have hσpow : σe.toEquiv ^ (2 ^ m) = 1 := by
    let σ : Equiv.Perm (ModV Q W) := σe.toEquiv
    have hσ_mk' : ∀ q : ↥Q, σ (QuotientGroup.mk q) = QuotientGroup.mk (φ q) := hσ_mk
    apply Equiv.ext
    intro v
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
    have hpow : ∀ k : ℕ, (σ ^ k) (QuotientGroup.mk q) =
        QuotientGroup.mk ((φ ^ k) q) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', Equiv.Perm.mul_apply, ih, hσ_mk', pow_succ']
          rfl
    rw [hpow, hφpow]
    simp
  exact ⟨φ, σe, hφ_coe, hσ_mk, hσpow⟩

private theorem modV_bot
    {L Q W : Subgroup G} [Finite ↥L]
    [hWnormal : (W.subgroupOf Q).Normal] [MulDistribMulAction ↥L ↥Q]
    [IsMulCommutative (ModV Q W)] [MulAction ↥L (ModV Q W)]
    (e : oTwoQuot ↥L ≃* alternatingGroup (Fin 5))
    (hQL : Q ≤ L) (hWn : L ≤ Subgroup.normalizer (W : Set G))
    (hfpf : ∀ x ∈ L, orderOf x = 3 → ∀ q ∈ Q, ⁅q, x⁆ ∈ W → q ∈ W)
    (hsmul : ∀ (l : ↥L) (q : ↥Q),
      ((l • q : ↥Q) : G) = (l : G) * (q : G) * (l : G)⁻¹)
    (hsmul_mk : ∀ (l : ↥L) (q : ↥Q),
      l • (QuotientGroup.mk q : ModV Q W) = QuotientGroup.mk (l • q))
    {φ : MulAut ↥Q} {σ : Equiv.Perm (ModV Q W)} {m : ℕ}
    (hσ_mk : ∀ q : ↥Q, σ (QuotientGroup.mk q) = QuotientGroup.mk (φ q))
    (hσ_one : σ (1 : ModV Q W) = 1) (hσpow : σ ^ (2 ^ m) = 1)
    (fbar : ModV Q W →* ModV Q W)
    (hfbar_mk : ∀ q : ↥Q, fbar (QuotientGroup.mk q) =
      QuotientGroup.mk (φ q * q⁻¹))
    (hfbar_smul : ∀ (l : ↥L) (v : ModV Q W), fbar (l • v) = l • fbar v)
    (hindex : W.relIndex Q = 16) :
    fbar.range = ⊥ := by
  let V : Type := ModV Q W
  haveI hQfin : Finite ↥Q :=
    Finite.of_injective (Subgroup.inclusion hQL) (Subgroup.inclusion_injective hQL)
  have hVcardNat : Nat.card V = 16 := hindex
  haveI : Fintype V := Fintype.ofFinite V
  have hVcard : Fintype.card V = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact hVcardNat
  have hker_ne : fbar.ker ≠ ⊥ :=
    modV_ker_ne_bot (L := L) (Q := Q) (W := W) hσ_mk hσ_one hσpow hVcardNat fbar hfbar_mk
  let R : Subgroup V := fbar.range
  have hRne_top : R ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective fbar := MonoidHom.range_eq_top.mp htop
    have hinj : Function.Injective fbar := Finite.injective_iff_surjective.mpr hsurj
    exact hker_ne ((MonoidHom.ker_eq_bot_iff fbar).mpr hinj)
  have hRdvd : Nat.card R ∣ 16 := by
    have h := Subgroup.card_subgroup_dvd_card R
    rwa [hVcardNat] at h
  have hRlt : Nat.card R < 16 := by
    have hlt : R < (⊤ : Subgroup V) := lt_of_le_of_ne le_top hRne_top
    have h := Subgroup.card_lt_of_lt hlt
    simpa [hVcard] using h
  obtain ⟨x, hx3⟩ := exists_orderOf_eq_three_of_oTwoQuot_mulEquiv e
  have hx3pow : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx3] at h
  have hxG3 : orderOf (x : G) = 3 := by
    rw [Subgroup.orderOf_coe, hx3]
  have hRsmul : ∀ (l : ↥L) (v : V), v ∈ R → l • v ∈ R := by
    intro l v hv
    change v ∈ fbar.range at hv
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hv
    rw [← hw, ← hfbar_smul]
    exact MonoidHom.mem_range.mpr ⟨l • w, rfl⟩
  let p : SubMulAction ↥L V :=
    { carrier := R, smul_mem' := fun l {v} hv => hRsmul l v hv }
  letI : MulAction ↥L ↥R := p.mulAction
  have hsmulR : ∀ (l : ↥L) (r : ↥R), ((l • r : ↥R) : V) = l • (r : V) := fun _ _ => rfl
  have hfreeR : ∀ r : ↥R, (x : ↥L) • r = r → r = 1 :=
    modV_free_of_fixed hQL hWn hfpf hsmul hsmul_mk hx3 R hsmulR
  have honeV : ∀ l : ↥L, l • (1 : V) = 1 := by
    intro l
    change l • (QuotientGroup.mk (1 : ↥Q) : V) = 1
    rw [hsmul_mk, smul_one]
    rfl
  have hmodR : Nat.card R ≡ 1 [MOD 3] :=
    modV_card_range_modEq_one (L := ↥L) (V := V) R hsmulR honeV hx3pow hfreeR
  exact modV_range_eq_bot (L := ↥L) (V := V) R hmodR hfreeR hRdvd hRlt hx3 e

private theorem modV_lift
    {Q W : Subgroup G} [hWnormal : (W.subgroupOf Q).Normal]
    {c : G} {φ : MulAut ↥Q}
    (hφ_coe : ∀ q : ↥Q, ((φ q : ↥Q) : G) = c * (q : G) * c⁻¹)
    (fbar : ModV Q W →* ModV Q W)
    (hfbar_mk : ∀ q : ↥Q, fbar (QuotientGroup.mk q) =
      QuotientGroup.mk (φ q * q⁻¹))
    (hbot : fbar.range = ⊥) :
    ∀ q ∈ Q, ⁅c, q⁆ ∈ W := by
  intro q hq
  let q' : ↥Q := ⟨q, hq⟩
  have hfq : fbar (QuotientGroup.mk q') = 1 := by
    have hmem : fbar (QuotientGroup.mk q') ∈ fbar.range :=
      MonoidHom.mem_range.mpr ⟨QuotientGroup.mk q', rfl⟩
    rwa [hbot, Subgroup.mem_bot] at hmem
  have hmemW : (φ q' * q'⁻¹ : ↥Q) ∈ W.subgroupOf Q := by
    rw [hfbar_mk] at hfq
    exact (QuotientGroup.eq_one_iff (N := W.subgroupOf Q) (x := φ q' * q'⁻¹)).mp hfq
  rw [Subgroup.mem_subgroupOf] at hmemW
  have hcoe : ((φ q' * q'⁻¹ : ↥Q) : G) = ⁅c, q⁆ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ_coe]
    simp only [commutatorElement_def]
    rfl
  rwa [hcoe] at hmemW

theorem commutatorElement_mem_of_fixFree_of_twoPow {L Q W : Subgroup G}
    [Finite ↥L] (e : oTwoQuot ↥L ≃* alternatingGroup (Fin 5))
    (hQL : Q ≤ L) (hQn : L ≤ Subgroup.normalizer (Q : Set G))
    (hWQ : W ≤ Q) (hWn : L ≤ Subgroup.normalizer (W : Set G))
    (hQW : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ W) (hindex : W.relIndex Q = 16)
    (hfpf : ∀ x ∈ L, orderOf x = 3 → ∀ q ∈ Q, ⁅q, x⁆ ∈ W → q ∈ W)
    {c : G} (hc2 : ∃ m, c ^ 2 ^ m = 1) (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hcW : c ∈ Subgroup.normalizer (W : Set G)) (hcL : ∀ l ∈ L, ⁅c, l⁆ ∈ Q) :
    ∀ q ∈ Q, ⁅c, q⁆ ∈ W := by
  classical
  obtain ⟨m, hm⟩ := hc2
  let S : ModVSetup L Q W := modVSetup hQL hQn hWQ hWn hQW
  letI : MulDistribMulAction ↥L ↥Q := S.smul
  have hsmul : ∀ (l : ↥L) (q : ↥Q),
      ((l • q : ↥Q) : G) = (l : G) * (q : G) * (l : G)⁻¹ := by
    intro l q
    exact Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨(l : G), hQn l.2⟩ q
  haveI : Finite ↥Q := S.qfin
  haveI : (W.subgroupOf Q).Normal := S.wnormal
  let V : Type := ModV Q W
  haveI : IsMulCommutative V := S.comm
  letI : CommGroup V := IsMulCommutative.instCommGroup
  haveI : MulAction.QuotientAction (X := ↥L) (G := ↥Q) (H := W.subgroupOf Q) :=
  { inv_mul_mem := by
      intro l a a' h
      rw [Subgroup.mem_subgroupOf] at h ⊢
      have hcoe : (((l • a)⁻¹ * (l • a') : ↥Q) : G) =
          (l : G) * ((a : G)⁻¹ * (a' : G)) * (l : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hsmul l a, hsmul l a']
        group
      rw [hcoe]
      exact (Subgroup.mem_normalizer_iff.mp (hWn l.2) _).mp h }
  letI : MulAction ↥L V :=
    MulAction.quotient (X := ↥L) (G := ↥Q) (H := W.subgroupOf Q)
  obtain ⟨φ, σe, hφ_coe, hσ_mk, hσpow⟩ :=
    modV_sigma_exists m hm hcQ hcW hWQ hWn
  let σ : Equiv.Perm V := σe.toEquiv
  have hσ_mk' : ∀ q : ↥Q, σ (QuotientGroup.mk q) = QuotientGroup.mk (φ q) := hσ_mk
  have hσ_one : σ (1 : V) = 1 := map_one σe
  have hsmul_mk : ∀ (l : ↥L) (q : ↥Q),
      l • (QuotientGroup.mk q : V) = QuotientGroup.mk (l • q) := by
    intro l q
    exact MulAction.Quotient.smul_mk (X := ↥L) (G := ↥Q) (H := W.subgroupOf Q) l q
  have hσ_smul : ∀ (l : ↥L) (v : V), σ (l • v) = l • σ v :=
    modV_sigma_smul hφ_coe hcQ hQn hQW hcL hsmul hsmul_mk σe hσ_mk'
  obtain ⟨fbar, hfbar_mk, hfbar_smul⟩ :=
    modV_fbar_exists hsmul_mk σe hσ_mk' hσ_smul
  have hbot : fbar.range = ⊥ :=
    modV_bot (m := m) e hQL hWn hfpf hsmul hsmul_mk hσ_mk' hσ_one hσpow fbar hfbar_mk
      hfbar_smul hindex
  exact modV_lift hφ_coe fbar hfbar_mk hbot
end CFSG.GroupTheory.AlternatingFive
