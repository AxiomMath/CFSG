module

public import CFSG.Quasithin.H13.L32NLem14333f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14333e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits CFSG.Quasithin.SL3Model
open scoped commutatorElement MatrixGroups

namespace L14333

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4
open CFSG.Quasithin.H13.L14333.Ctx_F4

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx_F4 G T L V V₂ K g a z b d x D)
include c

theorem mem_V_of_mul_self_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {p : G}
    (hp : p ∈ pCoreOf 2 L) (hp1 : p * p = 1) : p ∈ V := by
  obtain ⟨hP, hcard⟩ := c.pCoreOf_eq_F4 hyp
  have hVe : V = conjClosure (fsuV1 T V) L := hyp.V_eq
  rw [hP] at hp hcard
  exact mem_of_mul_self_eq_one c.X_comm_F4 (c.V_le_X_F4 hVe) (fun v hv => c.mul_self_V_F4 hv)
    c.sq_mem_V_of_X_F4 (c.exists_sq_F4 hVe) (by rw [hcard, c.card_V_F4]) hp hp1

theorem normalizer_le_normalizer_V_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hVP : V ≤ pCoreOf 2 L := le_sup_left.trans (c.sup_zU_le_P_F4 hyp)
  refine le_normalizer_of_conj_mem fun m hm v hv => ?_
  have hmP := normalizer_le_normalizer_pCoreOf 2 L hm
  have h1 : m * v * m⁻¹ ∈ pCoreOf 2 L := (Subgroup.mem_normalizer_iff.mp hmP v).mp (hVP hv)
  refine c.mem_V_of_mul_self_F4 hyp h1 ?_
  calc m * v * m⁻¹ * (m * v * m⁻¹) = m * (v * v) * m⁻¹ := by group
    _ = 1 := by rw [c.mul_self_V_F4 hv]; group

theorem exists_conj_eq_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {w : G}
    (hw : w ∈ V) (hw1 : w ≠ 1) : ∃ l ∈ L, l * z * l⁻¹ = w := by
  obtain ⟨D'⟩ := hyp.natural.nonempty_data
  have hne : ∀ (u : G) (hu : u ∈ V), u ≠ 1 → Multiplicative.toAdd (D'.ψ ⟨u, hu⟩) ≠ 0 := by
    intro u hu hu1 h
    apply hu1
    have h1 : D'.ψ ⟨u, hu⟩ = 1 := h
    have h2 := D'.ψ.injective (h1.trans (map_one D'.ψ).symm)
    exact congrArg Subtype.val h2
  obtain ⟨A, hA⟩ := exists_smul_eq3 _ _ (hne z c.z_mem_V_F4 c.z_ne) (hne w hw hw1)
  obtain ⟨⟨l, hl⟩, hlA⟩ := D'.surj A
  refine ⟨l, hl, ?_⟩
  have h1 := D'.equiv ⟨l, hl⟩ ⟨z, c.z_mem_V_F4⟩
  have h2 : D'.ψ (conjAct V ⟨l, D'.hnorm hl⟩ ⟨z, c.z_mem_V_F4⟩) = D'.ψ ⟨w, hw⟩ := by
    rw [h1, natAct3_apply, hlA, hA]
    rfl
  have h3 := congrArg Subtype.val (D'.ψ.injective h2)
  rwa [conjAct_coe_apply] at h3

theorem exists_inv_mul_mem_H_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V))
    {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) : ∃ l ∈ L, l⁻¹ * m ∈ l32nH T V := by
  obtain ⟨_, S⟩ := c.setting
  have hmV := c.normalizer_le_normalizer_V_F4 hyp hm
  have hw : m * z * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hmV z).mp c.z_mem_V_F4
  have hw1 : m * z * m⁻¹ ≠ 1 := fun h => c.z_ne (by
    calc z = m⁻¹ * (m * z * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨l, hl, hlz⟩ := c.exists_conj_eq_F4 hyp hw hw1
  refine ⟨l, hl, S.mem_g1_F4 c.z_mem c.z_ne ?_⟩
  calc l⁻¹ * m * z * (l⁻¹ * m)⁻¹ = l⁻¹ * (m * z * m⁻¹) * l := by group
    _ = z := by rw [← hlz]; group

theorem hatV_ne_F4 : (D.hat V).toAddSubgroup ≠ ⊥ ∧ (D.hat V).toAddSubgroup ≠ ⊤ := by
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  have hcard := c.card_hatV
  have hU16 : Nat.card D.V = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), c.dim, Nat.card_zmod]
    norm_num
  constructor
  · intro h
    have h1 : Nat.card ↥(D.hat V).toAddSubgroup = 1 := by rw [h]; exact AddSubgroup.card_bot
    have h2 : Nat.card ↥(D.hat V).toAddSubgroup = Nat.card ↥(D.hat V) := rfl
    omega
  · intro h
    have h1 : Nat.card ↥(D.hat V).toAddSubgroup = 16 := by
      rw [h, AddSubgroup.card_top, hU16]
    have h2 : Nat.card ↥(D.hat V).toAddSubgroup = Nat.card ↥(D.hat V) := rfl
    omega

theorem rho_mem_hatV_F4 {h : G} (hh : h ∈ l32nH T V) (hhV : h ∈ Subgroup.normalizer (V : Set G))
    {w : D.V} (hw : w ∈ D.hat V) : D.ρ ⟨h, l32nH_le_normalizer_fsuU T V hh⟩ w ∈ D.hat V := by
  obtain ⟨v, hv, rfl⟩ := c.exists_of_mem_hatV_F4 hw
  rw [D.ρ_π _ v (c.ctx.V_U hv)]
  have hv' : h * v * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hhV v).mp hv
  exact Submodule.subset_span ⟨h * v * h⁻¹, ⟨hv', c.ctx.V_U hv'⟩, rfl⟩

theorem not_img_le_F4 (Y : Subgroup G) (hYV : Y ≤ Subgroup.normalizer (V : Set G))
    (hKY : (K.subgroupOf (l32nH T V)).map (imgHom D) ≤ (Y.subgroupOf (l32nH T V)).map (imgHom D)) :
    False := by
  have hinv : ∀ k ∈ K, ∀ hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G),
      ∀ w ∈ (D.hat V).toAddSubgroup, D.ρ ⟨k, hkN⟩ w ∈ (D.hat V).toAddSubgroup := by
    intro k hk hkN w hw
    have hkH : k ∈ l32nH T V := le_of_mem_cComp c.comp hk
    obtain ⟨⟨y, hyH⟩, hy, hyk⟩ := hKY ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hyk' := congrArg Subtype.val hyk
    rw [imgHom_apply, imgHom_apply] at hyk'
    have : D.ρ ⟨k, hkN⟩ = D.ρ ⟨y, l32nH_le_normalizer_fsuU T V hyH⟩ := hyk'.symm
    rw [this]
    exact c.rho_mem_hatV_F4 hyH (hYV (Subgroup.mem_subgroupOf.mp hy)) hw
  rcases eq_bot_or_eq_top_of_invariant c.ii c.q_eq c.comp _ hinv with h | h
  · exact c.hatV_ne_F4.1 h
  · exact c.hatV_ne_F4.2 h

theorem card_img_H_F4 : Nat.card ↥(D.img (l32nH T V)) = 120 := card_img_l32nH c.ii

theorem card_img_T_F4 (hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V)) :
    Nat.card ↥((T.subgroupOf (l32nH T V)).map (imgHom D)) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥((T.subgroupOf (l32nH T V)).map (imgHom D)) :=
    (A4.isPGroup_subgroupOf_of_le hTS.1 hTS.2.1).map _
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hodd : Odd ((T.subgroupOf (l32nH T V)).map (imgHom D)).index := by
    have h := Subgroup.index_map_dvd (T.subgroupOf (l32nH T V)) (imgHom_surjective D)
    exact Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hTS.2.2)) h
  have h := Subgroup.card_mul_index ((T.subgroupOf (l32nH T V)).map (imgHom D))
  rw [hk, c.card_img_H_F4] at h
  have hk3 : k = 3 := two_pow_eq_of_mul_odd hodd (by decide : Odd 15)
    (h.trans (by norm_num))
  rw [hk, hk3]
  norm_num

theorem orderOf_img_x_F4 : orderOf (imgHom D ⟨x, c.x_mem_H_F4⟩) = 3 := by
  have h3 : (imgHom D ⟨x, c.x_mem_H_F4⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, c.x_mem_H_F4⟩ : ↥(l32nH T V)) ^ 3 = 1 := Subtype.ext (by simpa using c.x_cube)
    rw [this, map_one]
  have h1 : imgHom D ⟨x, c.x_mem_H_F4⟩ ≠ 1 := fun h =>
    c.x_ne_one_F4 (c.eq_one_of_imgHom_F4 c.x_mem_H_F4 (by decide) c.x_cube h)
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h1
  · exact h

theorem dvd_card_img_F4 {Y : Subgroup G} (hTY : T ≤ Y) (hxY : x ∈ Y)
    (hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V)) :
    24 ∣ Nat.card ↥((Y.subgroupOf (l32nH T V)).map (imgHom D)) := by
  have h8 : 8 ∣ Nat.card ↥((Y.subgroupOf (l32nH T V)).map (imgHom D)) := by
    rw [← c.card_img_T_F4 hTS]
    exact Subgroup.card_dvd_of_le (Subgroup.map_mono (Subgroup.subgroupOf_mono _ hTY))
  have h3 : 3 ∣ Nat.card ↥((Y.subgroupOf (l32nH T V)).map (imgHom D)) := by
    rw [← c.orderOf_img_x_F4]
    exact Subgroup.orderOf_dvd_natCard _ ⟨⟨x, c.x_mem_H_F4⟩, Subgroup.mem_subgroupOf.mpr hxY, rfl⟩
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8 h3

theorem card_img_inf_M_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V))
    (hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V)) :
    Nat.card ↥(((l32nH T V ⊓ Subgroup.normalizer (L : Set G)).subgroupOf (l32nH T V)).map
      (imgHom D)) = 24 := by
  set Y := l32nH T V ⊓ Subgroup.normalizer (L : Set G) with hY
  have hTY : T ≤ Y := le_inf hTS.1 c.T_le_normL_F4
  have hxY : x ∈ Y := ⟨c.x_mem_H_F4, Subgroup.le_normalizer c.x_mem⟩
  refine eq_24_of_dvd (c.dvd_card_img_F4 hTY hxY hTS) ?_ ?_
  · rw [← c.card_img_H_F4]
    exact Subgroup.card_subgroup_dvd_card _
  · intro h120
    have htop : (Y.subgroupOf (l32nH T V)).map (imgHom D) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (h120.trans c.card_img_H_F4.symm)
    exact c.not_img_le_F4 Y (inf_le_right.trans (c.normalizer_le_normalizer_V_F4 hyp)) (htop ▸ le_top)

theorem normalizer_L_le_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V))
    (hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V)) :
    Subgroup.normalizer (L : Set G) ≤ L ⊔ T := by
  set Y := l32nH T V ⊓ Subgroup.normalizer (L : Set G) with hY
  set J := (L ⊓ l32nH T V) ⊔ T with hJ
  have hJH : J ≤ l32nH T V := sup_le inf_le_right hTS.1
  have hJY : J ≤ Y :=
    sup_le (le_inf inf_le_right (inf_le_left.trans Subgroup.le_normalizer))
      (le_inf hTS.1 c.T_le_normL_F4)
  have hJ24 := c.dvd_card_img_F4 (le_sup_right : T ≤ J)
    (Subgroup.mem_sup_left ⟨c.x_mem, c.x_mem_H_F4⟩) hTS
  have hle : (J.subgroupOf (l32nH T V)).map (imgHom D) ≤
      (Y.subgroupOf (l32nH T V)).map (imgHom D) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ hJY)
  have heq : (J.subgroupOf (l32nH T V)).map (imgHom D) =
      (Y.subgroupOf (l32nH T V)).map (imgHom D) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [c.card_img_inf_M_F4 hyp hTS]
    exact Nat.le_of_dvd Nat.card_pos hJ24
  intro m hm
  obtain ⟨l, hl, hlm⟩ := c.exists_inv_mul_mem_H_F4 hyp hm
  have hlmY : l⁻¹ * m ∈ Y := ⟨hlm, mul_mem (Subgroup.le_normalizer (inv_mem hl)) hm⟩
  have hmem : imgHom D ⟨l⁻¹ * m, hlm⟩ ∈ (J.subgroupOf (l32nH T V)).map (imgHom D) := by
    rw [heq]
    exact ⟨⟨l⁻¹ * m, hlm⟩, Subgroup.mem_subgroupOf.mpr hlmY, rfl⟩
  obtain ⟨⟨j, hjH⟩, hj, hjm⟩ := hmem
  have hker : (⟨j, hjH⟩ : ↥(l32nH T V))⁻¹ * ⟨l⁻¹ * m, hlm⟩ ∈ (imgHom D).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hjm, inv_mul_cancel]
  rw [imgHom_ker, Subgroup.mem_subgroupOf, ← c.q_eq] at hker
  have hjJ : j ∈ J := Subgroup.mem_subgroupOf.mp hj
  have hq : j⁻¹ * (l⁻¹ * m) ∈ T := c.q_le hker
  have hm' : m = l * j * (j⁻¹ * (l⁻¹ * m)) := by group
  rw [hm']
  refine mul_mem (mul_mem (Subgroup.mem_sup_left hl) ?_) (Subgroup.mem_sup_right hq)
  exact (sup_le (inf_le_left.trans le_sup_left) le_sup_right : J ≤ L ⊔ T) hjJ

theorem K_inf_Q_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    K ⊓ pCoreOf 2 (l32nH T V) = fsuU T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_inf c.U_le_K_F4 (fsuU_le_pCoreOf c.ctx))
  rw [← c.pCoreOf_K_eq_F4 hyp]
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  exact fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 _ (le_of_mem_cComp c.comp hk)⟩

theorem mem_Q_of_comm_U_F4 {h : G} (hh : h ∈ l32nH T V) (hc : ∀ u ∈ fsuU T V, h * u = u * h) :
    h ∈ pCoreOf 2 (l32nH T V) := by
  rw [c.q_eq]
  refine (rho_eq_one_iff_mem (D := D) hh (l32nH_le_normalizer_fsuU T V hh)).mp ?_
  apply LinearEquiv.ext
  intro w
  obtain ⟨u, hu, rfl⟩ := D.π_surj w
  rw [D.ρ_π _ u hu]
  have : h * u * h⁻¹ = u := by rw [hc u hu]; group
  simp [this]

theorem comm_K_of_comm_U_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {t : G}
    (ht : t ∈ T) (htU : ∀ u ∈ fsuU T V, t * u = u * t) : ∀ k ∈ K, k * t = t * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htH : t ∈ l32nH T V := (c.ctx.T_le ht).1
  have hcent : oTwoUpper (l32nH T V) ≤ Subgroup.centralizer ({t} : Set G) := by
    refine (Subgroup.closure_le _).mpr fun k ⟨hkH, hko⟩ => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hkK : k ∈ K := c.odd_mem k hkH (orderOf k) hko (pow_orderOf_eq_one k)
    set e := k * t * k⁻¹ * t⁻¹ with he
    have heK : e ∈ K := by
      have h1 : t * k⁻¹ * t⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (c.K_norm htH) _).mp (K.inv_mem hkK)
      rw [he, show k * t * k⁻¹ * t⁻¹ = k * (t * k⁻¹ * t⁻¹) by group]
      exact K.mul_mem hkK h1
    have hkU : ∀ u ∈ fsuU T V, k⁻¹ * u * k ∈ fsuU T V := fun u hu => by
      have := (Subgroup.mem_normalizer_iff.mp
        (l32nH_le_normalizer_fsuU T V (inv_mem hkH)) u).mp hu
      simpa [mul_assoc] using this
    have heU : ∀ u ∈ fsuU T V, e * u = u * e := by
      intro u hu
      have h1 := htU _ (hkU u hu)
      have h2 := htU u hu
      calc e * u = k * t * k⁻¹ * t⁻¹ * u := rfl
        _ = k * t * (k⁻¹ * (t⁻¹ * u * t) * k) * k⁻¹ * t⁻¹ := by group
        _ = k * t * (k⁻¹ * u * k) * k⁻¹ * t⁻¹ := by
            rw [show t⁻¹ * u * t = u by rw [mul_assoc, ← h2]; group]
        _ = k * (t * (k⁻¹ * u * k)) * k⁻¹ * t⁻¹ := by group
        _ = k * ((k⁻¹ * u * k) * t) * k⁻¹ * t⁻¹ := by rw [h1]
        _ = u * e := by rw [he]; group
    have heQ : e ∈ pCoreOf 2 (l32nH T V) := c.mem_Q_of_comm_U_F4 (le_of_mem_cComp c.comp heK) heU
    have heZ : e ∈ centerOf (fsuU T V) := by
      have heU' : e ∈ fsuU T V := by rw [← c.K_inf_Q_F4 hyp]; exact ⟨heK, heQ⟩
      exact Subgroup.mem_inf.mpr ⟨heU', Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (heU u hu).symm⟩
    have hke : k * e * k⁻¹ = e :=
      odd_centralizes_of_card_four c.ctx c.card_zU k hkH hko e heZ
    have hkt : k * t * k⁻¹ = e * t := by rw [he]; group
    have hpow := pow_conj_eq hke hkt (orderOf k)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hpow
    have he1 : e ^ orderOf k = 1 := by
      have := congrArg (· * t⁻¹) hpow
      simpa using this.symm
    have hZ2 : IsPGroup 2 ↥(centerOf (fsuU T V)) := c.isPGroup_zU_F4
    obtain ⟨n, hn⟩ := hZ2 ⟨e, heZ⟩
    have hn' : e ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hcop : Nat.Coprime (2 ^ n) (orderOf k) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hko)
    have he1' : e = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hn')
        (orderOf_dvd_of_pow_eq_one he1))
    have : k * t * k⁻¹ = t := by rw [hkt, he1', one_mul]
    calc k * t = k * t * k⁻¹ * k := by group
      _ = t * k := by rw [this]
  intro k hk
  have := hcent (c.eq_oTwoUpper_F4 ▸ hk)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem centralizer_L_eq_bot_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨_, S⟩ := c.setting
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₁ := T ⊓ Subgroup.centralizer (L : Set G) with hC₁
  by_contra hne
  have hUL := c.U_le_L_F4 hyp
  have hKC : K ≤ Subgroup.normalizer (C₁ : Set G) := by
    refine le_normalizer_of_conj_mem fun k hk w hw => ?_
    have hwU : ∀ u ∈ fsuU T V, w * u = u * w := fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hw.2 u (hUL hu)).symm
    have := c.comm_K_of_comm_U_F4 hyp hw.1 hwU k hk
    rw [show k * w * k⁻¹ = w by rw [this]; group]
    exact hw
  have hLC : L ≤ Subgroup.normalizer (C₁ : Set G) := by
    refine le_normalizer_of_conj_mem fun l hl w hw => ?_
    have := Subgroup.mem_centralizer_iff.mp hw.2 l hl
    rw [show l * w * l⁻¹ = w by rw [this]; group]
    exact hw
  have hTC : T ≤ Subgroup.normalizer (C₁ : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, normalizer_le_normalizer_centralizer'' L (c.T_le_normL_F4 ht)⟩
  have hloc : IsTwoLocal (Subgroup.normalizer (C₁ : Set G)) :=
    ⟨C₁, hne, c.ctx.T2.to_le inf_le_left, rfl⟩
  obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := ((stmt13_3_2_two_of_stmt13_3_2_F4 S.h1332) G T L c.ctx.hyp.hyp.h13 L
    c.ctx.hyp.hyp.h13.faithful).2.2.2 M' hM' ((sup_le hLC hTC).trans hNM')
  have hKM : K ≤ Subgroup.normalizer (L : Set G) := hM'eq ▸ (hKC.trans hNM')
  have hKH : K ≤ l32nH T V := le_of_mem_cComp c.comp
  exact c.not_img_le_F4 (l32nH T V ⊓ Subgroup.normalizer (L : Set G))
    (inf_le_right.trans (c.normalizer_le_normalizer_V_F4 hyp))
    (Subgroup.map_mono (Subgroup.subgroupOf_mono _ (le_inf hKH hKM)))

end Ctx_F4

end L14333

end CFSG.Quasithin.H13
