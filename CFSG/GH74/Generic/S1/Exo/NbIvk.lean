module

public import CFSG.GH74.Generic.S1.Exo.NbShape
public import CFSG.GH74.Generic.S1.Exo.NbQ8
public import CFSG.GH74.Generic.S1.Exo.NbCentral
public import CFSG.GH74.Generic.S1.Exo.NbOrder
public import CFSG.GH74.GLS.LU.Local.KStepGHDefs

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG Subgroup CFSG.GH74 CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement

theorem nb_isCompIn_of_subnormal {G : Type*} [Group G] {X D K : Subgroup G} (hDX : D ≤ X)
    (hD : (D.subgroupOf X).IsSubnormal) (hK : IsCompIn D K) : IsCompIn X K := by
  refine ⟨hK.1.trans hDX, ?_⟩
  have h1 : CFSG.IsComponent ((K.subgroupOf X).subgroupOf (D.subgroupOf X)) :=
    (CFSG.GH74.GLS.LU.Local.isComponent_subgroupOf_iff' hDX).2 hK.2
  have hq : CFSG.IsQuasisimple ↥(K.subgroupOf X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hK.1).trans (Subgroup.subgroupOfEquivOfLe (hK.1.trans hDX)).symm)
      hK.2.1
  exact ⟨hq, Subgroup.IsSubnormal.trans (Subgroup.subgroupOf_mono X hK.1) h1.2 hD⟩

theorem nb_le_pPrimeCore_of_odd {G : Type} [Group G] [Finite G] {S : Subgroup G} (hS : S.IsSubnormal)
    (hodd : Odd (Nat.card S)) : S ≤ pPrimeCore 2 G := by
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hS
  have htop : CFSG.pPrimeCore 2 S = ⊤ := by
    apply le_antisymm le_top
    apply le_sSup
    exact ⟨Subgroup.normal_top, by
      rw [Subgroup.card_top]
      exact Nat.coprime_two_left.mpr hodd⟩
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact h1

theorem nb_isPGroup_center_component {H : Type} [Group H] [Finite H] (hO : pPrimeCore 2 H = ⊥)
    {K : Subgroup H} (hK : IsComponent K) : IsPGroup 2 (center ↥K) := by
  rw [IsPGroup.iff_orderOf]
  intro g
  have hm : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hm
  have h2a : (2 : ℕ) ^ a ≠ 0 := by positivity
  have hg' : orderOf (g ^ 2 ^ a) = b := by
    rw [orderOf_pow' _ h2a, hab, Nat.gcd_eq_right (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (by positivity)]
  set x : H := (((g ^ 2 ^ a : ↥(center ↥K)) : ↥K) : H) with hx
  have hxK : x ∈ K := (((g ^ 2 ^ a : ↥(center ↥K)) : ↥K)).2
  have hord : orderOf x = b := by
    rw [hx, orderOf_coe, orderOf_coe, hg']
  set S : Subgroup H := Subgroup.zpowers x with hS
  have hSK : S ≤ K := (Subgroup.zpowers_le).2 hxK
  have hcard : Odd (Nat.card S) := by
    rw [hS, Nat.card_zpowers, hord]; exact hb
  have hSn : (S.subgroupOf K).Normal := by
    refine ⟨fun n hn k => ?_⟩
    obtain ⟨m, hm'⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hn' : n = ((g ^ 2 ^ a : ↥(center ↥K)) : ↥K) ^ m := by
      apply Subtype.ext
      have hm'' : x ^ m = (n : H) := hm'
      rw [← hm'']
      simp [hx]
    have hz : n ∈ center ↥K := by
      rw [hn']; exact Subgroup.zpow_mem _ ((g ^ 2 ^ a : ↥(center ↥K))).2 m
    have hcomm : k * n * k⁻¹ = n := by
      have := Subgroup.mem_center_iff.1 hz k
      calc k * n * k⁻¹ = n * k * k⁻¹ := by rw [this]
        _ = n := by group
    rw [hcomm]; exact hn
  have hsub : S.IsSubnormal :=
    Subgroup.IsSubnormal.trans hSK (Subgroup.Normal.isSubnormal hSn) hK.2
  have hle := nb_le_pPrimeCore_of_odd hsub hcard
  rw [hO] at hle
  have hx1 : x = 1 := by
    have : x ∈ (⊥ : Subgroup H) := hle (Subgroup.mem_zpowers x)
    simpa using this
  have : (g ^ 2 ^ a : ↥(center ↥K)) = 1 := by
    apply Subtype.ext; apply Subtype.ext; simpa [hx] using hx1
  rw [this, orderOf_one] at hg'
  refine ⟨a, ?_⟩
  rw [hab, ← hg']; simp

theorem nb_isPGroup_zpowers {X : Type*} [Group X] {v : X} {n : ℕ} (h : v ^ (2 ^ n) = 1) :
    IsPGroup 2 (Subgroup.zpowers v) := by
  have hord : orderOf v ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem nb_card_sup_dvd {H : Type*} [Group H] {A B : Subgroup H} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) ∣ Nat.card ↥A * Nat.card ↥B := by
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => hAB a a.2 b b.2)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr, ← Nat.card_prod]
  exact Subgroup.card_range_dvd _

namespace NbhdHyp

variable {H : Type} [Group H] [Finite H] {q : ℕ} {w y : H} {J₂ J₄ : Subgroup H}
  (h : NbhdHyp H q w y J₂ J₄)

include h

theorem le_J₄_of_le_sup {K : Subgroup H} (hperf : Group.IsPerfect ↥K) (hle : K ≤ J₂ ⊔ J₄)
    (hc : ∀ a ∈ K, ∀ c ∈ J₂, a * c = c * a) : K ≤ J₄ := by
  refine nb_perfect_le_of_comm_pair (Z := Subgroup.zpowers w) ?_ ?_ hperf ?_
  · intro k hk z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_right (show Commute k w from (h.comm w h.w_mem k hk).symm) n).eq
  · intro z hz z' hz'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
    exact ((Commute.refl w).zpow_zpow n m).eq
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := nb_mem_sup_of_commute h.comm (hle hg)
    have hac : ∀ c ∈ J₂, a * c = c * a := by
      intro c hc'
      have h1 := hc _ hg c hc'
      have e : b * c = c * b := (h.comm c hc' b hb).symm
      have : (a * c) * b = (c * a) * b := by
        calc a * c * b = a * (c * b) := by rw [mul_assoc]
          _ = a * (b * c) := by rw [e]
          _ = a * b * c := by rw [mul_assoc]
          _ = c * (a * b) := h1
          _ = c * a * b := by rw [mul_assoc]
      exact mul_right_cancel this
    have hab : a * b = b * a := h.comm a ha b hb
    rcases h.cent₂ a ha hac with h1 | h1
    · exact ⟨b, hb, 1, Subgroup.one_mem _, by rw [h1]; simp⟩
    · exact ⟨b, hb, w, Subgroup.mem_zpowers w, by rw [h1] at hab ⊢; exact hab⟩

theorem isCompIn_le_sup {L : Subgroup H} (hL : IsCompIn (centralizer ({w * y} : Set H)) L) :
    L ≤ J₂ ⊔ J₄ := by
  have hb := h.bal _ hL.2
  intro g hg
  exact hb ⟨⟨g, hL.1 hg⟩, hg, rfl⟩

theorem lay_inf_cent {N₂ : Subgroup H} (hN₂ : IsComponent N₂)
    (hcomm : ∀ a ∈ J₂, ∀ b ∈ N₂, a * b = b * a) (hJ₄ : J₄ ≤ N₂) :
    (layer ↥(N₂ ⊓ centralizer ({w * y} : Set H))).map
      (N₂ ⊓ centralizer ({w * y} : Set H)).subtype = J₄ := by
  set X := centralizer ({w * y} : Set H) with hX
  set D := N₂ ⊓ X with hD
  have hDX : D ≤ X := inf_le_right
  have hDsub : (D.subgroupOf X).IsSubnormal := by
    have : (N₂.subgroupOf X).IsSubnormal := hN₂.2.subgroupOf
    rwa [← Subgroup.inf_subgroupOf_right N₂ X] at this
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    have hle : layer ↥D ≤ J₄.comap D.subtype := by
      refine sSup_le fun K hK => ?_
      set K' : Subgroup H := K.map D.subtype with hK'
      have hK'D : K' ≤ D := Subgroup.map_subtype_le K
      have hK'eq : K'.subgroupOf D = K := Subgroup.comap_map_eq_self_of_injective D.subtype_injective K
      have hcomp : IsCompIn D K' := ⟨hK'D, by rw [hK'eq]; exact hK⟩
      have hcompX : IsCompIn X K' := nb_isCompIn_of_subnormal hDX hDsub hcomp
      have hleJ : K' ≤ J₂ ⊔ J₄ := h.isCompIn_le_sup hcompX
      have hq : CFSG.IsQuasisimple ↥K' :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (K.equivMapOfInjective D.subtype D.subtype_injective) hK.1
      have hc : ∀ a ∈ K', ∀ c ∈ J₂, a * c = c * a := fun a ha c hc' =>
        (hcomm c hc' a (hK'D ha).1).symm
      have hJ : K' ≤ J₄ := h.le_J₄_of_le_sup hq.1 hleJ hc
      intro k hk
      exact hJ ⟨k, hk, rfl⟩
    exact hle hx
  · exact CFSG.GH74.GLS.LU.Local.le_layer_of_isCompIn
      (CFSG.GH74.GLS.LU.Local.isCompIn_mono' ⟨h.J₄_le_cent, h.comp₄⟩ (le_inf hJ₄ h.J₄_le_cent) hDX)

theorem y_not_central {N₂ : Subgroup H} (hN₂ : IsComponent N₂)
    (hcomm : ∀ a ∈ J₂, ∀ b ∈ N₂, a * b = b * a) (hJ₄ : J₄ ≤ N₂) (hne : J₄ ≠ N₂) :
    (⟨y, hJ₄ h.y_mem⟩ : ↥N₂) ∉ center ↥N₂ := by
  intro hc
  have hX : N₂ ≤ centralizer ({w * y} : Set H) := by
    intro a ha
    rw [h.mem_cent_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨a, ha⟩)
  have hle := h.comp_le hN₂ hX
  have hJ : N₂ ≤ J₄ := h.le_J₄_of_le_sup hN₂.1.1 hle (fun a ha c hc' => (hcomm c hc' a ha).symm)
  exact hne (le_antisymm hJ₄ hJ)


theorem lay_cent_N {N₂ : Subgroup H} (hN₂ : IsComponent N₂)
    (hcomm : ∀ a ∈ J₂, ∀ b ∈ N₂, a * b = b * a) (hJ₄ : J₄ ≤ N₂) :
    (layer ↥(centralizer ({(⟨y, hJ₄ h.y_mem⟩ : ↥N₂)} : Set ↥N₂))).map
      (centralizer ({(⟨y, hJ₄ h.y_mem⟩ : ↥N₂)} : Set ↥N₂)).subtype = J₄.subgroupOf N₂ := by
  set y' : ↥N₂ := ⟨y, hJ₄ h.y_mem⟩ with hy'
  set D : Subgroup ↥N₂ := centralizer ({y'} : Set ↥N₂) with hD
  have hDmap : D.map N₂.subtype = N₂ ⊓ centralizer ({w * y} : Set H) := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n.2, (h.mem_cent_iff _).2 ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.1 hn
      exact congrArg Subtype.val this
    · rintro ⟨hg1, hg2⟩
      refine ⟨⟨g, hg1⟩, ?_, rfl⟩
      show (⟨g, hg1⟩ : ↥N₂) ∈ D
      rw [hD, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext ((h.mem_cent_iff g).1 hg2)
  have h1 := nb_lay_map_injective N₂.subtype N₂.subtype_injective D
  rw [hDmap, h.lay_inf_cent hN₂ hcomm hJ₄] at h1
  have h2 := Subgroup.comap_map_eq_self_of_injective N₂.subtype_injective
    ((layer ↥D).map D.subtype)
  rw [← h1] at h2
  exact h2.symm


theorem Ez_eq {N₂ : Subgroup H} (hN₂ : IsComponent N₂)
    (hcomm : ∀ a ∈ J₂, ∀ b ∈ N₂, a * b = b * a) (hJ₄ : J₄ ≤ N₂) :
    IVK.Ez (QuotientGroup.mk' (center ↥N₂) (⟨y, hJ₄ h.y_mem⟩ : ↥N₂)) =
      (J₄.subgroupOf N₂).map (QuotientGroup.mk' (center ↥N₂)) := by
  have h1 := nb_layer_cent_map (QuotientGroup.mk' (center ↥N₂)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (⟨y, hJ₄ h.y_mem⟩ : ↥N₂)
  unfold IVK.Ez
  rw [h1, h.lay_cent_N hN₂ hcomm hJ₄]

theorem mk_injOn {N₂ : Subgroup H} (hN₂ : IsComponent N₂)
    (hcomm : ∀ a ∈ J₂, ∀ b ∈ N₂, a * b = b * a) (hJ₄ : J₄ ≤ N₂) (hne : J₄ ≠ N₂) :
    Function.Injective ((QuotientGroup.mk' (center ↥N₂)).comp (J₄.subgroupOf N₂).subtype) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, ha⟩ hker
  have hz : a ∈ center ↥N₂ := (QuotientGroup.eq_one_iff a).1 hker
  have ha4 : (a : H) ∈ J₄ := ha
  have hc : ∀ b ∈ J₄, (a : H) * b = b * (a : H) := fun b hb =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨b, hJ₄ hb⟩)).symm
  rcases h.cent₄ _ ha4 hc with h1 | h1
  · exact Subtype.ext (Subtype.ext h1)
  · exfalso
    apply h.y_not_central hN₂ hcomm hJ₄ hne
    have : a = ⟨y, hJ₄ h.y_mem⟩ := Subtype.ext h1
    rw [← this]
    exact hz


theorem hasSL2Model_Ez {N₂ : Subgroup H} (hN₂ : IsComponent N₂)
    (hcomm : ∀ a ∈ J₂, ∀ b ∈ N₂, a * b = b * a) (hJ₄ : J₄ ≤ N₂) (hne : J₄ ≠ N₂) :
    HasSL2Model ↥(IVK.Ez (QuotientGroup.mk' (center ↥N₂) (⟨y, hJ₄ h.y_mem⟩ : ↥N₂)))
      (fun r => r = q) := by
  set φ := (QuotientGroup.mk' (center ↥N₂)).comp (J₄.subgroupOf N₂).subtype with hφ
  have hinj : Function.Injective φ := h.mk_injOn hN₂ hcomm hJ₄ hne
  have hrange : φ.range = (J₄.subgroupOf N₂).map (QuotientGroup.mk' (center ↥N₂)) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hEz := h.Ez_eq hN₂ hcomm hJ₄
  let e : ↥(IVK.Ez (QuotientGroup.mk' (center ↥N₂) (⟨y, hJ₄ h.y_mem⟩ : ↥N₂))) ≃* ↥J₄ :=
    ((MulEquiv.subgroupCongr (hEz.trans hrange.symm)).trans (MonoidHom.ofInjective hinj).symm).trans
      (Subgroup.subgroupOfEquivOfLe hJ₄)
  obtain ⟨F, hF1, hF2, hq, ⟨eJ⟩⟩ := h.sl₄
  exact ⟨F, hF1, hF2, hq, ⟨e.trans eJ⟩⟩


theorem cyclic_sylow {N₂ : Subgroup H} (hN₂ : IsComponent N₂)
    (hcomm : ∀ a ∈ J₂, ∀ b ∈ N₂, a * b = b * a) (hJ₄ : J₄ ≤ N₂)
    (hZ : IsPGroup 2 (center ↥N₂)) :
    ∀ S : Sylow 2 ↥(centralizer ((IVK.Ez (QuotientGroup.mk' (center ↥N₂)
        (⟨y, hJ₄ h.y_mem⟩ : ↥N₂)) : Subgroup (↥N₂ ⧸ center ↥N₂)) : Set (↥N₂ ⧸ center ↥N₂))),
      IsCyclic ↥S := by
  set π := QuotientGroup.mk' (center ↥N₂) with hπ
  set y' : ↥N₂ := ⟨y, hJ₄ h.y_mem⟩ with hy'
  set E := IVK.Ez (π y') with hE
  set D := centralizer (E : Set (↥N₂ ⧸ center ↥N₂)) with hD
  have hEeq : E = (J₄.subgroupOf N₂).map π := h.Ez_eq hN₂ hcomm hJ₄
  intro S
  have hJ4perf : Group.IsPerfect ↥(J₄.subgroupOf N₂) := by
    have : Group.IsPerfect ↥J₄ := h.J₄_perf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJ₄).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJ₄).symm.surjective
  have hkey : ∀ s : ↥D, s ∈ (S : Subgroup ↥D) →
      (s : ↥N₂ ⧸ center ↥N₂) ∈ Subgroup.zpowers (π y') := by
    intro s hs
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨s, hs⟩
    have hsk : (s : ↥N₂ ⧸ center ↥N₂) ^ (2 ^ k) = 1 := by
      have h1 : (⟨s, hs⟩ : ↥S) ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
      have h2 := congrArg (fun z : ↥S => ((z : ↥D) : ↥N₂ ⧸ center ↥N₂)) h1
      simpa using h2
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (s : ↥N₂ ⧸ center ↥N₂)
    have hg₀2 : ∃ n : ℕ, g₀ ^ (2 ^ n) = 1 := by
      have hz : g₀ ^ (2 ^ k) ∈ center ↥N₂ := by
        rw [← QuotientGroup.ker_mk' (center ↥N₂)]
        rw [MonoidHom.mem_ker, map_pow]
        have : π g₀ = (s : ↥N₂ ⧸ center ↥N₂) := hg₀
        rw [this]; exact hsk
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hZ) ⟨g₀ ^ (2 ^ k), hz⟩
      refine ⟨k + j, ?_⟩
      have h3 : (⟨g₀ ^ (2 ^ k), hz⟩ : ↥(center ↥N₂)) ^ (2 ^ j) = 1 := by
        rw [← hj]; exact pow_orderOf_eq_one _
      have h4 := congrArg (fun z : ↥(center ↥N₂) => ((z : ↥(center ↥N₂)) : ↥N₂)) h3
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h4
      rw [pow_add, pow_mul]
      exact h4
    obtain ⟨n, hn⟩ := hg₀2
    have hπg : π g₀ = (s : ↥N₂ ⧸ center ↥N₂) := hg₀
    have hcomm4' : ∀ a' ∈ J₄.subgroupOf N₂, a' * g₀ = g₀ * a' := by
      intro a' ha'
      have hpa : π a' ∈ E := by
        rw [hEeq]; exact Subgroup.mem_map_of_mem _ ha'
      have hX : ⁅J₄.subgroupOf N₂, Subgroup.zpowers g₀⁆ ≤ center ↥N₂ := by
        rw [Subgroup.commutator_le]
        intro b hb x hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [← QuotientGroup.ker_mk' (center ↥N₂), MonoidHom.mem_ker]
        have hpb : π b ∈ E := by
          rw [hEeq]; exact Subgroup.mem_map_of_mem _ hb
        have hc : π b * π g₀ = π g₀ * π b := by
          have := Subgroup.mem_centralizer_iff.1 s.2 (π b) hpb
          rw [hπg]; exact this
        have hcj : Commute (π b) (π (g₀ ^ j)) := by
          rw [map_zpow]; exact (show Commute (π b) (π g₀) from hc).zpow_right j
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 hcj.eq
      have hbot : ⁅⁅J₄.subgroupOf N₂, Subgroup.zpowers g₀⁆, J₄.subgroupOf N₂⁆ = ⊥ := by
        rw [eq_bot_iff]
        calc ⁅⁅J₄.subgroupOf N₂, Subgroup.zpowers g₀⁆, J₄.subgroupOf N₂⁆
            ≤ ⁅center ↥N₂, J₄.subgroupOf N₂⁆ := Subgroup.commutator_mono hX le_rfl
          _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2
                (Subgroup.center_le_centralizer _)
      have h0 := CFSG.LocalCores.perfect_double_commutator hJ4perf hbot
      have h1 := Subgroup.commutator_mem_commutator ha' (Subgroup.mem_zpowers g₀)
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hc₄ : ∀ b ∈ J₄, b * (g₀ : H) = (g₀ : H) * b := by
      intro b hb
      have := hcomm4' ⟨b, hJ₄ hb⟩ hb
      exact congrArg Subtype.val this
    have hT : IsPGroup 2 ((Subgroup.zpowers g₀).map N₂.subtype) :=
      (nb_isPGroup_zpowers hn).map N₂.subtype
    have hc₂' : ∀ t ∈ (Subgroup.zpowers g₀).map N₂.subtype, ∀ a ∈ J₂, t * a = a * t := by
      rintro _ ⟨x, hx, rfl⟩ a ha
      exact (hcomm a ha x x.2).symm
    have hc₄' : ∀ t ∈ (Subgroup.zpowers g₀).map N₂.subtype, ∀ b ∈ J₄, t * b = b * t := by
      rintro _ ⟨x, hx, rfl⟩ b hb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hcb : Commute b (g₀ : H) := hc₄ b hb
      have : Commute b ((g₀ ^ j : ↥N₂) : H) := by
        rw [Subgroup.coe_zpow]; exact hcb.zpow_right j
      exact this.symm.eq
    have hcase := h.two_subgroup_le hT hc₂' hc₄' (g₀ : H) ⟨g₀, Subgroup.mem_zpowers g₀, rfl⟩
    rw [hπg.symm]
    rcases hcase with h1 | h1 | h1 | h1
    · have : g₀ = 1 := Subtype.ext h1
      rw [this, map_one]; exact Subgroup.one_mem _
    · have hwN : w ∈ N₂ := h1 ▸ g₀.2
      have hcen : g₀ ∈ center ↥N₂ := by
        rw [Subgroup.mem_center_iff]
        intro n
        apply Subtype.ext
        change (n : H) * (g₀ : H) = (g₀ : H) * (n : H)
        rw [h1]; exact h.w_central n
      have h0 : π g₀ = 1 := (QuotientGroup.eq_one_iff g₀).2 hcen
      rw [h0]; exact Subgroup.one_mem _
    · have : g₀ = y' := Subtype.ext h1
      rw [this]; exact Subgroup.mem_zpowers _
    · have hwN : w ∈ N₂ := by
        have : w = (g₀ : H) * y := by rw [h1, mul_assoc, h.y_sq, mul_one]
        rw [this]; exact N₂.mul_mem g₀.2 (hJ₄ h.y_mem)
      have hwc : (⟨w, hwN⟩ : ↥N₂) ∈ center ↥N₂ := by
        rw [Subgroup.mem_center_iff]
        intro n
        exact Subtype.ext (h.w_central n)
      have hg : g₀ = ⟨w, hwN⟩ * y' := Subtype.ext h1
      have h0 : π ⟨w, hwN⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hwc
      rw [hg, map_mul, h0, one_mul]
      exact Subgroup.mem_zpowers _
  let ψ : ↥(S : Subgroup ↥D) →* ↥(Subgroup.zpowers (π y')) :=
    (D.subtype.comp (S : Subgroup ↥D).subtype).codRestrict (Subgroup.zpowers (π y'))
      (fun s => hkey s.1 s.2)
  have hψ : Function.Injective ψ := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  exact isCyclic_of_injective ψ hψ


theorem shape (hnc : NoCommonComponent J₂ J₄) (h95 : LU.Local.IVK_9_5At_gh q) :
    ∃ N₂ : Subgroup H, IsComponent J₂ ∧ IsComponent N₂ ∧ layer H = J₂ ⊔ N₂ ∧ J₄ ≤ N₂ ∧ J₄ ≠ N₂ ∧
      (∀ a ∈ J₂, ∀ b ∈ N₂, a * b = b * a) ∧ (∀ K, IsComponent K → K = J₂ ∨ K = N₂) ∧
      ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ IVK.IsLnEps 3 (↥N₂ ⧸ center ↥N₂) δ q := by
  obtain ⟨N₂, hJ₂c, hN₂c, hlayer, hJ₄N, hne, hcomm, hall⟩ := h.struct hnc
  refine ⟨N₂, hJ₂c, hN₂c, hlayer, hJ₄N, hne, hcomm, hall, ?_⟩
  have hsimple : IsSimpleGroup (↥N₂ ⧸ center ↥N₂) := hN₂c.1.2.1
  have hnonab : ∃ a b : ↥N₂ ⧸ center ↥N₂, a * b ≠ b * a := hN₂c.1.2.2
  have hKnat : IsKGroupNative (↥N₂ ⧸ center ↥N₂) :=
    SectionRank.IsKGroupCat.quotient (SectionRank.IsKGroupCat.subgroup h.kgroup N₂) (center ↥N₂)
  have hGH : GHList (↥N₂ ⧸ center ↥N₂) := h.gh N₂ (center ↥N₂) hsimple hnonab
  have hZ : IsPGroup 2 (center ↥N₂) := nb_isPGroup_center_component h.core hN₂c
  have hy : (⟨y, hJ₄N h.y_mem⟩ : ↥N₂) ∉ center ↥N₂ := h.y_not_central hN₂c hcomm hJ₄N hne
  have hz2 : orderOf (QuotientGroup.mk' (center ↥N₂) (⟨y, hJ₄N h.y_mem⟩ : ↥N₂)) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have : (⟨y, hJ₄N h.y_mem⟩ : ↥N₂) ^ 2 = 1 := by
        rw [pow_two]; exact Subtype.ext h.y_sq
      rw [this, map_one]
    · intro h1
      exact hy ((QuotientGroup.eq_one_iff _).1 h1)
  exact h95 (↥N₂ ⧸ center ↥N₂) hsimple hKnat hGH _ hz2 h.odd
    (h.hasSL2Model_Ez hN₂c hcomm hJ₄N hne) (h.cyclic_sylow hN₂c hcomm hJ₄N hZ)

theorem no_prime (hnc : NoCommonComponent J₂ J₄) (h95 : LU.Local.IVK_9_5At_gh q) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ q ^ 2 + 1) : ¬ r ∣ Nat.card ↥(layer H) := by
  obtain ⟨N₂, hJ₂c, hN₂c, hlayer, hJ₄N, hne, hcomm, hall, δ, hδ, hL3⟩ := h.shape hnc h95
  obtain ⟨p, n, hp, hn, hq⟩ := nb_q_prime_pow h.sl₂
  have hq2 : r ∣ (p ^ n) ^ 2 + 1 := hq ▸ hrq
  intro hdvd
  have hsl : HasSL2Model ↥J₂ (fun r => r = p ^ n) := hq ▸ h.sl₂
  have hZ : IsPGroup 2 (center ↥N₂) := nb_isPGroup_center_component h.core hN₂c
  have hL3' : IVK.IsLnEps 3 (↥N₂ ⧸ center ↥N₂) δ (p ^ n) := hq ▸ hL3
  have hdiv : Nat.card ↥(layer H) ∣ Nat.card ↥J₂ * (Nat.card (center ↥N₂) * Nat.card (↥N₂ ⧸ center ↥N₂)) := by
    rw [hlayer]
    have h1 := nb_card_sup_dvd hcomm
    have h2 : Nat.card ↥N₂ = Nat.card (center ↥N₂) * Nat.card (↥N₂ ⧸ center ↥N₂) := by
      rw [mul_comm]; exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥N₂))
    rw [h2] at h1
    exact h1
  have hrd := hr.dvd_mul.1 (dvd_trans hdvd hdiv)
  rcases hrd with h1 | h1
  · exact nb_not_dvd_card_sl2 hp hsl hr hr2 hq2 h1
  · rcases hr.dvd_mul.1 h1 with h2 | h2
    · obtain ⟨k, hk⟩ := hZ.exists_card_eq
      rw [hk] at h2
      have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2)
      exact hr2 this
    · exact nb_not_dvd_card_of_isLnEps3 hp hδ hL3' hr hr2 hq2 h2

end NbhdHyp

end CFSG.GH74.Generic.S1.Exo
