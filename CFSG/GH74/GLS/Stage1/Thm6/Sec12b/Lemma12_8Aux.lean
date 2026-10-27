module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.CoreE
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.After

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

section Aux

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

theorem mem_normalizer_of_forward {H : Subgroup G} {g : G} (h : ∀ e ∈ H, g * e * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨fun he => h e he, fun he => ?_⟩
  let φ : H → H := fun e' => ⟨g * e' * g⁻¹, h e' e'.2⟩
  have hinj : Function.Injective φ := by
    intro e1 e2 h12
    apply Subtype.ext
    exact conj_inj g (congrArg Subtype.val h12)
  obtain ⟨e', he'⟩ := Finite.injective_iff_surjective.1 hinj ⟨g * e * g⁻¹, he⟩
  have h3 : g * (e' : G) * g⁻¹ = g * e * g⁻¹ := congrArg Subtype.val he'
  rw [← conj_inj g h3]
  exact e'.2

theorem exists_central_invol (h : HBase G x S T P Q Rd F) :
    ∃ y ∈ S, y ≠ 1 ∧ y * y = 1 ∧ ∀ s ∈ S, y * s = s * y := by
  have hS : S ≠ ⊥ := by
    intro hbot
    apply h.x_ne_one
    have hx : x ∈ S := h.T_le_S h.x_mem_T
    rw [hbot, Subgroup.mem_bot] at hx
    exact hx
  exact exists_central_involution_of_normal h.S_pgroup le_rfl
    (fun t ht n hn => S.mul_mem (S.mul_mem ht hn) (S.inv_mem ht)) hS

theorem not_conjTo_central (h : HBase G x S T P Q Rd F) (hTS : T ≠ S) {y : G}
    (hyc : ∀ s ∈ S, y * s = s * y) : ¬ ConjTo x y := by
  rintro ⟨g, hg⟩
  have hcent : ∀ s ∈ S, s ∈ Subgroup.centralizer ({y} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hyc s hs
  have hsyl := h.sylow_cent_of_conj (y := y) (g := g⁻¹) (by simpa using hg)
    (fun t ht => hcent t (h.T_le_S ht))
  have := sylow2_eq_of_le hsyl h.S_pgroup h.T_le_S (fun s hs => hcent s hs)
  exact hTS this.symm

theorem E_le_T (h : HBase G x S T P Q Rd F) {V : Subgroup G} (hVP : V ≤ P) :
    V ⊔ Subgroup.zpowers x ≤ T :=
  sup_le (hVP.trans h.P_le_T) ((Subgroup.zpowers_le).2 h.x_mem_T)

theorem card_E (h : HBase G x S T P Q Rd F) {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) :
    Nat.card (V ⊔ Subgroup.zpowers x : Subgroup G) = 8 := by
  have hxV : x ∉ V := fun hx => h.x_not_mem_P (hVP hx)
  have hc : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right
      (show Commute a x from (h.x_central a (h.P_le_T (hVP ha))).symm) k).eq
  have hd : V ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcV, hcx⟩
    rcases zpowers_sq_cases h.x_sq hcx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hcV hxV
  rw [card_sup_of_commute hc hd, hV.2, card_zpowers_of_sq h.x_sq h.x_ne_one]

theorem omegaZ_le_E (h : HBase G x S T P Q Rd F) (h127 : After127 G x z S T P Q Rd F)
    {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) (hzV : z ∈ V) :
    omegaZ T ≤ V ⊔ Subgroup.zpowers x := by
  rcases h127.card_Z with h4 | h8
  · rw [h127.Z_eq h4]
    exact sup_le le_sup_right ((Subgroup.zpowers_le).2 (Subgroup.mem_sup_left hzV))
  · have hTZ := h127.T_eq_Z h8
    have hT8 : Nat.card ↥T = 8 := (congrArg (fun K : Subgroup G => Nat.card ↥K) hTZ).trans h8
    have hEq : V ⊔ Subgroup.zpowers x = T :=
      Subgroup.eq_of_le_of_card_ge (E_le_T h hVP) (by rw [hT8, card_E h hVP hV])
    exact (hTZ.symm.trans hEq.symm).le

end Aux

section App

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

theorem exists_ctx (h : HBase G x S T P Q Rd F) (h127 : After127 G x z S T P Q Rd F)
    (hf3 : IP_f3 x P) (hzV : IP_z_V z P) {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V)
    {a : G} (haS : a ∈ S) (haT : a ∉ T)
    (haN : a ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) :
    ∃ f y : G, Ctx V x f a y := by
  obtain ⟨f, hf3', hfx, hfV, hfn⟩ := hf3 V hVP hV
  obtain ⟨y, hyS, hy1, hy2, hyc⟩ := exists_central_invol h
  have hxV : x ∉ V := fun hx => h.x_not_mem_P (hVP hx)
  have hxcomm : ∀ w ∈ V, x * w = w * x := fun w hw => h.x_central w (h.P_le_T (hVP hw))
  have hfx' : f * x * f⁻¹ = x := by rw [hfx]; group
  have hfN : f ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
    apply mem_normalizer_of_forward
    intro e he
    have hle : V ⊔ Subgroup.zpowers x ≤ Hconj f (V ⊔ Subgroup.zpowers x) :=
      sup_le (fun w hw => mem_Hconj.2 (Subgroup.mem_sup_left (hfV w hw)))
        ((Subgroup.zpowers_le).2 (mem_Hconj.2 (by
          rw [hfx']; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x))))
    exact mem_Hconj.1 (hle he)
  have hyT : y ∈ T := h.extremal y hyS (hyc x (h.T_le_S h.x_mem_T))
  have hyZ : y ∈ omegaZ T := ⟨hyT, hy2, fun t ht => hyc t (h.T_le_S ht)⟩
  have hyE : y ∈ V ⊔ Subgroup.zpowers x := omegaZ_le_E h h127 hVP hV (hzV V hVP hV) hyZ
  have hya : a * y * a⁻¹ = y := by
    rw [← hyc a haS]; group
  have hax : a * x * a⁻¹ ≠ x := by
    intro hh
    apply haT
    apply h.extremal a haS
    calc a * x = (a * x * a⁻¹) * a := by group
      _ = x * a := by rw [hh]
  exact ⟨f, y, ⟨hV, h.x_sq, hxcomm, hxV, hf3', hfx', hfV, hfn, haN, hfN, hax, hyE, hy1, hya,
    not_conjTo_central h h127.T_ne_S hyc⟩⟩

theorem fusion_V (h : HBase G x S T P Q Rd F) (h127 : After127 G x z S T P Q Rd F)
    (hf3 : IP_f3 x P) (hzV : IP_z_V z P) {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V)
    {a : G} (haS : a ∈ S) (haT : a ∉ T)
    (haN : a ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) :
    ∀ v ∈ V, ∃ g : G, g ∈ Subgroup.centralizer (V : Set G) ∧
      g ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ∧
        g * x * g⁻¹ = x * v := by
  obtain ⟨f, y, c⟩ := exists_ctx h h127 hf3 hzV hVP hV haS haT haN
  intro v hv
  obtain ⟨g, hgN, hgV, hgx⟩ := c.words v hv
  refine ⟨g, ?_, hgN, hgx⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  calc w * g = (g * w * g⁻¹) * g := by rw [hgV w hw]
    _ = g * w := by group

end App

section Count

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem ncard_conj_mul_card_inf_centralizer (N : Subgroup G) (g : G) :
    {y | ∃ n ∈ N, n * g * n⁻¹ = y}.ncard *
      Nat.card (N ⊓ Subgroup.centralizer {g} : Subgroup G) = Nat.card N := by
  let _ : MulAction N G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp N.subtype)
  have hsmul : ∀ (x : N) (y : G), x • y = (x : G) * y * (x : G)⁻¹ := fun x y =>
    ConjAct.toConjAct_smul (x : G) y
  have horb : MulAction.orbit N g = {y | ∃ x ∈ N, x * g * x⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, (hsmul x g).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hsmul _ g⟩
  have hstab : MulAction.stabilizer N g = (Subgroup.centralizer {g}).subgroupOf N := by
    ext x
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have h := (MulAction.stabilizer N g).index_mul_card
  rw [MulAction.index_stabilizer, horb, hstab, ← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  exact h

end Count

section Sylow

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

theorem two_lt_relIndex_of_sylow (h : HBase G x S T P Q Rd F) {V : Subgroup G} {f a y : G}
    (c : Ctx V x f a y)
    (hsyl : IsSylow2In (S ⊓ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))
      (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))) :
    2 < T.relIndex S := by
  by_contra hle'
  have hle : T.relIndex S ≤ 2 := not_lt.1 hle'
  set N : Subgroup G := Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) with hN
  set K : Subgroup G := S ⊓ N with hK
  have hset : {y | ∃ n ∈ N, n * x * n⁻¹ = y} = (fun u => x * u) '' (V : Set G) := by
    ext y'
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hnE : n * x * n⁻¹ ∈ V ⊔ Subgroup.zpowers x := Ctx.conjE hn Ctx.x_mem_E
      have hnc : ConjTo x (n * x * n⁻¹) := ⟨n, rfl⟩
      rcases c.E_cases hnE with hV' | ⟨w, hw, hw'⟩
      · exact absurd hnc ((c.V_iff hnE).1 hV')
      · exact ⟨w, hw, hw'.symm⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨g, hgN, _, hgx⟩ := c.words u hu
      exact ⟨g, hgN, hgx⟩
  have hncard : {y | ∃ n ∈ N, n * x * n⁻¹ = y}.ncard = 4 := by
    rw [hset, Set.ncard_image_of_injective _ (mul_right_injective x)]
    have e : Nat.card (V : Set G) = Nat.card V := rfl
    rw [← Nat.card_coe_set_eq, e]
    exact c.hV.2
  have h4 : 4 * Nat.card (N ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) =
      Nat.card N := by
    have := ncard_conj_mul_card_inf_centralizer N x
    rwa [hncard] at this
  have hKN : K ≤ N := inf_le_right
  have h5 : K.relIndex N * Nat.card K = Nat.card N := by
    have := Subgroup.relIndex_mul_card (H := K) (K := N)
    rwa [inf_of_le_left hKN] at this
  have hodd : ¬ 2 ∣ K.relIndex N := hsyl.2.2
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥(T ⊓ N) = 2 ^ k := by
    obtain ⟨j, hj⟩ := h.T_pgroup.exists_card_eq
    have hdvd : Nat.card ↥(T ⊓ N) ∣ Nat.card ↥T := Subgroup.card_dvd_of_le inf_le_left
    rw [hj] at hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, hk⟩
  have hle1 : T ⊓ N ≤ N ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans h.T_le_C)
  have hdvd2 : 2 ^ k ∣ Nat.card (N ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    rw [← hk]; exact Subgroup.card_dvd_of_le hle1
  have hdvd3 : 2 ^ (k + 2) ∣ K.relIndex N * Nat.card K := by
    rw [h5, ← h4, pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm (2 ^ k) 4]
    exact Nat.mul_dvd_mul_left 4 hdvd2
  have hcop : Nat.Coprime (2 ^ (k + 2)) (K.relIndex N) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hdvd4 : 2 ^ (k + 2) ∣ Nat.card K := hcop.dvd_of_dvd_mul_left hdvd3
  have hge : 2 ^ (k + 2) ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos hdvd4
  have hTNK : (T ⊓ N) ⊓ K = T ⊓ N := inf_eq_left.2 (inf_le_inf_right N h.T_le_S)
  have hTK : T ⊓ N = T ⊓ K := by
    rw [hK, ← inf_assoc, inf_eq_left.2 h.T_le_S]
  have hT0 : T.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : (T ⊓ N).relIndex K ≤ 2 := by
    rw [hTK, Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right inf_le_left hT0).trans hle
  have hub : Nat.card K ≤ 2 * 2 ^ k := by
    have h6 := Subgroup.relIndex_mul_card (H := T ⊓ N) (K := K)
    rw [hTNK, hk] at h6
    calc Nat.card K = (T ⊓ N).relIndex K * 2 ^ k := h6.symm
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_right _ hrel
  have hpos : 0 < 2 ^ k := by positivity
  rw [pow_add] at hge
  generalize 2 ^ k = m at *
  omega

theorem sylow_of_normal (h : HBase G x S T P Q Rd F) {V : Subgroup G} {a : G} (haS : a ∈ S)
    (haT : a ∉ T)
    (haN : a ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))
    (hnorm : NormalIn (V ⊔ Subgroup.zpowers x) T) (hrel : T.relIndex S ≤ 2) :
    IsSylow2In (S ⊓ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))
      (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) := by
  have hTN : ∀ t ∈ T, t ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_of_forward
    intro e he
    exact hnorm.2 t ht e he
  have hSN : S ≤ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro s hs
    by_cases hsT : s ∈ T
    · exact hTN s hsT
    · have hmul : a⁻¹ * s ∈ T :=
        relIndex_two_mul_mem hrel (S.inv_mem haS) hs
          (fun hh => haT (by simpa using T.inv_mem hh)) hsT
      have : s = a * (a⁻¹ * s) := by group
      rw [this]
      exact mul_mem haN (hTN _ hmul)
  rw [inf_of_le_left hSN]
  obtain ⟨P', hP', hSP'⟩ := exists_sylow2_ge h.S_pgroup hSN
  have : P' = S := sylow2_eq_of_le h.S_sylow hP'.2.1 hSP' le_top
  rw [this] at hP'
  exact hP'

end Sylow

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
