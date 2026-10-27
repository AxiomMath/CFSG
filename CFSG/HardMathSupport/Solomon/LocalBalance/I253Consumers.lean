module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3U512
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.NarrowI253

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem s1_tilde (i145 : Input14_5) (i253 : Input25_3_27) {m : ℕ} (hS : GLStanding G m 3) {b : G} (hb3 : orderOf b = 3)
    {x : G} (hx1 : x ≠ 1) {Js J₁ J₂ : Subgroup G} (hJs : GLAPComponent 3 (Cb x) Js)
    (h₁ : GLAPComponent 3 (Js ⊓ Cb b) J₁) (h₂ : GLAPComponent 3 (Js ⊓ Cb b) J₂) (hne : J₁ ≠ J₂)
    (hb₁ : b ∈ J₁) (hb₂ : b ∈ J₂) (hε₁ : IsSL3Eps (barOf 3 J₁))
    (hZ₁ : Subgroup.center (barOf 3 J₁) = Subgroup.zpowers (QuotientGroup.mk (⟨b, hb₁⟩ : ↥J₁)))
    (hn₂ : ∃ a ∈ J₂, a ^ 3 = 1 ∧ a ∉ Subgroup.zpowers b) :
    ∃ y ∈ J₂, y ^ 3 = 1 ∧ y ∉ Subgroup.zpowers b ∧ b ∉ oPrimePOf 3 (Js ⊓ Cb y) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hJ₂le : J₂ ≤ Js ⊓ Cb b := h₂.1
  have hbJs : b ∈ Js := (h₁.1 hb₁).1
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hJsne : Js ≠ ⊤ := by
    intro htop
    have hCx : Cb x = ⊤ := top_le_iff.1 (htop ▸ hJs.1)
    have hxc : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Cb x := hCx ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_singleton_iff.1 this)
    have := hS.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact hx1 (Subgroup.mem_bot.1 (h ▸ hxc))
    · obtain ⟨u, v, huv⟩ := hS.nonabelian
      exact huv (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top u) v).symm
  set b' : ↥Js := ⟨b, hbJs⟩ with hb'
  set A_H : Subgroup ↥Js := Subgroup.centralizer ({b'} : Set ↥Js) with hAH
  have hAmap : A_H.map Js.subtype = Js ⊓ Cb b := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx))⟩
    · rintro ⟨hgJ, hgC⟩
      exact ⟨⟨g, hgJ⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hgC)), rfl⟩
  obtain ⟨J₁', hJ₁', rfl⟩ := exists_glaPComponent_map_eq hp Js.subtype (s1t_ker_sub Js A_H)
    (K' := J₁) (by rw [hAmap]; exact h₁)
  obtain ⟨J₂', hJ₂', rfl⟩ := exists_glaPComponent_map_eq hp Js.subtype (s1t_ker_sub Js A_H)
    (K' := J₂) (by rw [hAmap]; exact h₂)
  set π : ↥Js →* (↥Js ⧸ GLAPPrimeCore 3 ↥Js) := QuotientGroup.mk' (GLAPPrimeCore 3 ↥Js) with hπ
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hb3')
  have hbt3 : π b' ^ 3 = 1 := by rw [← map_pow, hb'3, map_one]
  have hbt1 : π b' ≠ 1 := by
    intro h1
    have hmem : b' ∈ GLAPPrimeCore 3 ↥Js := (QuotientGroup.eq_one_iff b').1 h1
    have hord : orderOf b' = 3 := orderOf_eq_prime hb'3 (by
      intro h
      have h' : b = 1 := congrArg Subtype.val h
      rw [h'] at hb3
      simp at hb3)
    have h2 : orderOf (⟨b', hmem⟩ : ↥(GLAPPrimeCore 3 ↥Js)) = 3 := by
      rw [Subgroup.orderOf_mk, hord]
    have h3 : 3 ∣ Nat.card (GLAPPrimeCore 3 ↥Js) :=
      Dvd.dvd.trans (by rw [h2]) (orderOf_dvd_natCard (⟨b', hmem⟩ : ↥(GLAPPrimeCore 3 ↥Js)))
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_gLAPPrimeCore_aux 3 ↥Js) h3
  have hbtord : orderOf (π b') = 3 := orderOf_eq_prime hbt3 hbt1
  set CY : Subgroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js) :=
    Subgroup.centralizer ({π b'} : Set (↥Js ⧸ GLAPPrimeCore 3 ↥Js)) with hCY
  have hAπ : A_H.map π = CY := s1t_map_cent hb'3
  have hKJs : CFSG.Open.IsKGroup ↥Js := isKGroup_of_isKProper hS.kProper hJsne
  have hKY : CFSG.Open.IsKGroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js) := s1t_isKGroup_quotient hKJs _
  have hcoreY : GLAPPrimeCore 3 (↥Js ⧸ GLAPPrimeCore 3 ↥Js) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hcommY := i145 (↥Js ⧸ GLAPPrimeCore 3 ↥Js) (s1t_isKGroup_of_open hKY) hcoreY (π b') hbt3
  have hc₁ : GLAPComponent 3 CY (J₁'.map π) :=
    hAπ ▸ glaPComponent_map hp π (s1t_ker_pi A_H) hJ₁'
  have hc₂ : GLAPComponent 3 CY (J₂'.map π) :=
    hAπ ▸ glaPComponent_map hp π (s1t_ker_pi A_H) hJ₂'
  have hq₁ := s1t_isQuasisimple hc₁ hcommY
  have hq₂ := s1t_isQuasisimple hc₂ hcommY
  have hcomp₁ : IsComponentOf (J₁'.map π) CY := ⟨hc₁.1, hc₁.2.1, hq₁⟩
  have hcomp₂ : IsComponentOf (J₂'.map π) CY := ⟨hc₂.1, hc₂.2.1, hq₂⟩
  have hne' : J₁'.map π ≠ J₂'.map π := by
    intro heq
    apply hne
    congr 1
    have hb₁' := lcEquiv_barX hp π A_H (s1t_ker_pi A_H) hJ₁'.1
    have hb₂' := lcEquiv_barX hp π A_H (s1t_ker_pi A_H) hJ₂'.1
    have hbar : barX 3 A_H J₁' = barX 3 A_H J₂' := by
      apply Subgroup.map_injective (lcEquiv hp π A_H (s1t_ker_pi A_H)).injective
      show (barX 3 A_H J₁').map (lcMonoidHom hp π A_H (s1t_ker_pi A_H)) =
        (barX 3 A_H J₂').map (lcMonoidHom hp π A_H (s1t_ker_pi A_H))
      rw [hb₁', hb₂', heq]
    exact glaPComponent_uniqueAux hJ₁' hJ₂' hbar
  have hcomm12 : ⁅J₁'.map π, J₂'.map π⁆ = ⊥ := s1t_comm_of_ne hcomp₁ hcomp₂ hne'
  have hb'₁ : b' ∈ J₁' := by
    obtain ⟨x, hx, hxb⟩ := hb₁
    exact (Subtype.ext hxb : x = b') ▸ hx
  have hb'₂ : b' ∈ J₂' := by
    obtain ⟨x, hx, hxb⟩ := hb₂
    exact (Subtype.ext hxb : x = b') ▸ hx
  obtain ⟨a, ha₂, ha3, hanot⟩ := hn₂
  have haJs : a ∈ Js := (hJ₂le ha₂).1
  have haC : a * b = b * a := Subgroup.mem_centralizer_singleton_iff.1 (hJ₂le ha₂).2
  obtain ⟨a', ha'₂, ha'a⟩ := ha₂
  have ha'eq : a' = ⟨a, haJs⟩ := Subtype.ext ha'a
  have hat3 : π a' ^ 3 = 1 := by
    rw [← map_pow]
    have ha'a' : (a' : G) = a := ha'a
    have : a' ^ 3 = 1 := Subtype.ext (by
      simp only [Subgroup.coe_pow, Subgroup.coe_one]; rw [ha'a']; exact ha3)
    rw [this, map_one]
  have hat_mem : π a' ∈ J₂'.map π := ⟨a', ha'₂, rfl⟩
  have hbt_mem₁ : π b' ∈ J₁'.map π := ⟨b', hb'₁, rfl⟩
  have hbt_mem₂ : π b' ∈ J₂'.map π := ⟨b', hb'₂, rfl⟩
  have hat_comm : π a' * π b' = π b' * π a' :=
    Subgroup.mem_centralizer_singleton_iff.1 (hc₂.1 hat_mem)
  have hat_not : π a' ∉ Subgroup.zpowers (π b') := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hanot
    refine q_mem_zpowers_of_bar (X := Js) (b := b) (g := a) hbJs (kb := 1)
      (by simpa using hb3') haJs (k := 1) (by simpa using ha3) haC ?_
    refine ⟨b' ^ k, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ?_
      have h1 : ((b' ^ k : ↥Js) : G) = b ^ k := Subgroup.coe_zpow _ _ _
      rw [h1]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
    · show π (b' ^ k) = QuotientGroup.mk (⟨a, haJs⟩ : ↥Js)
      rw [map_zpow, hk, ha'eq]
      rfl
  have hcm : Commute (π b') (π a') := hat_comm.symm
  have hcomm_zp : ∀ h ∈ Subgroup.zpowers (π b'), h * π a' = π a' * h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hcm.zpow_left k).eq
  have hzea : IsElemAbelian 3 (Subgroup.zpowers (π b')) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbt3, one_zpow]
  have hA'card : Nat.card ↥(Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a')) = 9 := by
    rw [card_sup_zpowers_of_pow_three_eq_one hat3 hat_not hcomm_zp, Nat.card_zpowers, hbtord]
  have hA'ea : IsElemAbelian 3 (Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a')) :=
    isElemAbelian_sup_zpowers hzea hat3 hcomm_zp
  have hA'norm : Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a') ≤
      Subgroup.normalizer ((⊤ : Subgroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js)) : Set _) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hcent : Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a') ≤
      Subgroup.centralizer ((J₁'.map π : Subgroup _) : Set _) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      exact Subgroup.mem_centralizer_singleton_iff.1 (hc₁.1 hh)
    · have h21 : ⁅J₂'.map π, J₁'.map π⁆ = ⊥ := (Subgroup.commutator_comm _ _).trans hcomm12
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h21 hat_mem
  have hfield : ∀ a₀ ∈ Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a'), a₀ ≠ 1 →
      InducesFieldAut 3 (J₁'.map π) a₀ := fun a₀ h _ => s1t_inducesFieldAut _ (hcent h)
  have hYq : CFSG.Open.IsQuasisimple (↥Js ⧸ GLAPPrimeCore 3 ↥Js) :=
    isQuasisimple_quotient_of_glaPComponent hJs
  have hKq : CFSG.IsQuasisimple ↥(⊤ : Subgroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js)) :=
    s1t_isQuasisimple_of_open
      (CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        Subgroup.topEquiv.symm hYq)
  have hKk : CFSG.IsKGroup ↥(⊤ : Subgroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js)) :=
    s1t_isKGroup_of_open (s1t_isKGroup_of_subgroup hKY ⊤)
  have hcomp₁' : IsComponentOf (J₁'.map π) (⊤ ⊓ Subgroup.centralizer ({π b'} :
      Set (↥Js ⧸ GLAPPrimeCore 3 ↥Js))) := by
    rw [top_inf_eq]; exact hcomp₁
  let e : barOf 3 (J₁'.map Js.subtype) ≃* (↥(J₁'.map π) ⧸ GLAPPrimeCore 3 ↥(J₁'.map π)) :=
    (lcEquiv hp Js.subtype J₁' (s1t_ker_sub Js J₁')).symm.trans
      (lcEquiv hp π J₁' (s1t_ker_pi J₁'))
  have he_b : e (QuotientGroup.mk ⟨b, hb₁⟩) = QuotientGroup.mk ⟨π b', hbt_mem₁⟩ := by
    have h1 : (lcEquiv hp Js.subtype J₁' (s1t_ker_sub Js J₁')).symm
        (QuotientGroup.mk ⟨b, hb₁⟩) = QuotientGroup.mk ⟨b', hb'₁⟩ := by
      rw [MulEquiv.symm_apply_eq]; rfl
    have h2 : e (QuotientGroup.mk ⟨b, hb₁⟩) = lcEquiv hp π J₁' (s1t_ker_pi J₁')
        ((lcEquiv hp Js.subtype J₁' (s1t_ker_sub Js J₁')).symm (QuotientGroup.mk ⟨b, hb₁⟩)) := rfl
    rw [h2, h1]; rfl
  have hε : IsSL3Eps (↥(J₁'.map π) ⧸ GLAPPrimeCore 3 ↥(J₁'.map π)) :=
    s1t_isSL3Eps_of_equiv e hε₁
  have hZ : Subgroup.center (↥(J₁'.map π) ⧸ GLAPPrimeCore 3 ↥(J₁'.map π)) =
      Subgroup.zpowers (QuotientGroup.mk (⟨π b', hbt_mem₁⟩ : ↥(J₁'.map π))) := by
    rw [← s1t_center_map e, hZ₁, MonoidHom.map_zpowers]
    congr 1
  have key := i253 (↥Js ⧸ GLAPPrimeCore 3 ↥Js) ⊤ (J₁'.map π)
    (Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a')) (π b') hKq hKk (Subgroup.mem_top _)
    hbtord hcomp₁' hbt_mem₁ hε hZ hA'norm hA'ea hA'card
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) hfield
    (i253_su38Trivial_of_centralizes hcent)
  rcases key with htop | ⟨a₀, ha₀, ha₀1, hnot⟩
  ·
    exfalso
    have h21 : ⁅J₂'.map π, J₁'.map π⁆ = ⊥ := (Subgroup.commutator_comm _ _).trans hcomm12
    have hle : ⁅J₂'.map π, J₂'.map π⁆ ≤ ⁅J₂'.map π, J₁'.map π⁆ :=
      Subgroup.commutator_mono le_rfl (htop ▸ le_top)
    rw [h21, le_bot_iff, glaPComponent_perfect hc₂] at hle
    apply hat_not
    have : π a' ∈ J₂'.map π := hat_mem
    rw [hle] at this
    rw [Subgroup.mem_bot.1 this]
    exact Subgroup.one_mem _
  ·
    have hnorm_zp : Subgroup.zpowers (π b') ≤ Subgroup.normalizer
        ((Subgroup.zpowers (π a') : Subgroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js)) : Set _) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact ((hcm.zpow_zpow k j).symm).eq
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm_zp
    have ha₀' := ha₀
    rw [← SetLike.mem_coe, hmul] at ha₀'
    obtain ⟨u, hu, v, hv, huv⟩ := ha₀'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hv
    have hba' : Commute b' a' := by
      show b' * a' = a' * b'
      rw [ha'eq]; exact Subtype.ext haC.symm
    set y₀ : ↥Js := b' ^ i * a' ^ j with hy₀
    have hy₀J : y₀ ∈ J₂' :=
      J₂'.mul_mem (Subgroup.zpow_mem _ hb'₂ i) (Subgroup.zpow_mem _ ha'₂ j)
    have hy₀3 : y₀ ^ 3 = 1 := by
      rw [hy₀, (hba'.zpow_zpow i j).mul_pow, s1t_zpow_three hb'3 i, s1t_zpow_three
        (show a' ^ 3 = 1 from Subtype.ext (by
          simp only [Subgroup.coe_pow, Subgroup.coe_one]; rw [show (a' : G) = a from ha'a]; exact ha3)) j,
        one_mul]
    have hπy₀ : π y₀ = a₀ := by
      rw [hy₀, map_mul, map_zpow, map_zpow, hi, hj]; exact huv
    subst hπy₀
    refine ⟨(y₀ : G), ⟨y₀, hy₀J, rfl⟩, ?_, ?_, ?_⟩
    · have := congrArg Subtype.val hy₀3
      simpa using this
    · intro hyb
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyb
      have hy₀k : y₀ = b' ^ k := Subtype.ext hk.symm
      have hmemz : π y₀ ∈ Subgroup.zpowers (π b') :=
        Subgroup.mem_zpowers_iff.2 ⟨k, by rw [hy₀k, map_zpow]⟩
      apply hnot
      have hbt_in : π b' ∈ Subgroup.zpowers (π y₀) := s1t_mem_zpowers_of_prime hbtord hmemz ha₀1
      refine mem_oPrimePOf_of_forall_comm hp ?_ ?_
      · refine ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.1 hmemz
        rw [← hk']
        exact (Commute.self_zpow (π b') k').eq
      · intro w hw
        have hwc : Commute w (π y₀) := Subgroup.mem_centralizer_singleton_iff.1 hw.2
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hbt_in
        rw [← hm]
        exact ((hwc.zpow_right m).symm).eq
    · intro hmem
      apply hnot
      let φ : ↥(Js ⊓ Cb (y₀ : G)) →* ↥(⊤ ⊓ Subgroup.centralizer ({π y₀} :
          Set (↥Js ⧸ GLAPPrimeCore 3 ↥Js))) :=
        MonoidHom.codRestrict (π.comp (Subgroup.inclusion inf_le_left)) _ (fun g => by
          refine ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
          show π (Subgroup.inclusion inf_le_left g) * π y₀ = π y₀ * π (Subgroup.inclusion inf_le_left g)
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2.2))
      have hφ : Function.Surjective φ := by
        intro w
        have hw : w.1 ∈ (Subgroup.centralizer ({y₀} : Set ↥Js)).map π := by
          rw [s1t_map_cent hy₀3]; exact w.2.2
        obtain ⟨g, hg, hgw⟩ := hw
        have hgc : (g : G) * (y₀ : G) = (y₀ : G) * (g : G) :=
          congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
        exact ⟨⟨(g : G), g.2, Subgroup.mem_centralizer_singleton_iff.2 hgc⟩, Subtype.ext hgw⟩
      have hle := o_map_hom_le φ hφ
      obtain ⟨o, ho, hob⟩ := hmem
      refine ⟨φ o, hle (Subgroup.mem_map_of_mem φ ho), ?_⟩
      show π (Subgroup.inclusion inf_le_left o) = π b'
      congr 1
      exact Subtype.ext hob


section S1Sec

omit [Finite G] in
private theorem s1_eps_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSL3Eps X) : IsSL3Eps Y := by
  obtain ⟨hs, hc⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hs with ⟨K, f, fin, ⟨φ⟩⟩ | ⟨K, f, fin, q, hq, ⟨φ⟩⟩
    · exact Or.inl ⟨K, f, fin, ⟨e.symm.trans φ⟩⟩
    · exact Or.inr ⟨K, f, fin, q, hq, ⟨e.symm.trans φ⟩⟩
  · have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
      Subgroup.map_center_eq e
    rw [← hcen, Subgroup.card_map_of_injective e.injective]
    exact hc

omit [Finite G] in
private theorem s1_center_zpowers {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X)
    (hZ : Subgroup.center Y = Subgroup.zpowers (e x)) :
    Subgroup.center X = Subgroup.zpowers x := by
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq e
  have hz : Subgroup.zpowers (e x) = (Subgroup.zpowers x).map e.toMonoidHom :=
    (MonoidHom.map_zpowers e.toMonoidHom x).symm
  rw [hZ, hz] at hcen
  exact Subgroup.map_injective e.injective hcen

private theorem s1_E {C A : Subgroup G} (hAC : A ≤ C) :
    ∃ E : (↥A ⧸ GLAPPrimeCore 3 ↥A) ≃*
        (↥(barX 3 C A) ⧸ GLAPPrimeCore 3 ↥(barX 3 C A)),
      ∀ g (hgA : g ∈ A) (hgC : g ∈ C),
        E (QuotientGroup.mk ⟨g, hgA⟩) =
          QuotientGroup.mk ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨g, hgC⟩,
            ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.2 hgA, rfl⟩⟩ := by
  have hker : Nat.Coprime 3 (Nat.card ↥(A.subgroupOf C ⊓
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)).ker)) := by
    refine (coprime_card_gLAPPrimeCore_aux 3 ↥C).coprime_dvd_right ?_
    have : A.subgroupOf C ⊓ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)).ker ≤
        GLAPPrimeCore 3 ↥C := by
      rw [QuotientGroup.ker_mk']
      exact inf_le_right
    exact Subgroup.card_dvd_of_le this
  let e1 := lcEquiv Nat.prime_three (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)) (A.subgroupOf C) hker
  let e0 := Subgroup.subgroupOfEquivOfLe hAC
  let qA := QuotientGroup.congr (GLAPPrimeCore 3 ↥A) (GLAPPrimeCore 3 ↥(A.subgroupOf C)) e0.symm
    (glaPPrimeCore_map_iso 3 e0.symm)
  refine ⟨qA.trans e1, fun g hgA hgC => ?_⟩
  rfl

omit [Finite G] in
private theorem s1_cast {H : Type*} [Group H] (S T : Subgroup H) (h : S = T) :
    ∃ f : (↥S ⧸ GLAPPrimeCore 3 ↥S) ≃* (↥T ⧸ GLAPPrimeCore 3 ↥T),
      ∀ s (hs : s ∈ S) (ht : s ∈ T), f (QuotientGroup.mk ⟨s, hs⟩) = QuotientGroup.mk ⟨s, ht⟩ := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ _ _ => rfl⟩

omit [Finite G] in
private theorem s1_barX_zpowers {C : Subgroup G} {b : G} (hbC : b ∈ C) (v : ↥C ⧸ GLAPPrimeCore 3 ↥C) :
    v ∈ barX 3 C (Subgroup.zpowers b) ↔
      v ∈ Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_subgroupOf.1 hc
    refine ⟨n, ?_⟩
    have : (⟨b, hbC⟩ : ↥C) ^ n = c := Subtype.ext (by simpa using hn)
    simp only
    rw [← map_zpow, this]
  · rintro ⟨n, rfl⟩
    refine ⟨⟨b, hbC⟩ ^ n, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
    exact ⟨n, by simp⟩

private theorem s1_center_barOf {C L : Subgroup G} {b : G} (hL : GLAPComponent 3 C L)
    (hbC : b ∈ C) (hbL : b ∈ L)
    (hF : FusData (barX 3 C L) (barX 3 C (Subgroup.zpowers b))) :
    Subgroup.center (↥L ⧸ GLAPPrimeCore 3 ↥L) =
      Subgroup.zpowers (QuotientGroup.mk (⟨b, hbL⟩ : ↥L)) := by
  let φ := quotEquivBarX Nat.prime_three hL.1 hL.2.1
  have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩ ∈ barX 3 C L :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hbL, rfl⟩
  have hφ : φ (QuotientGroup.mk ⟨b, hbL⟩) =
      ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩, hmem⟩ := rfl
  refine s1_center_zpowers φ _ ?_
  rw [hφ]
  ext w
  rw [Subgroup.mem_center_iff]
  have h1 := hF.Zcenter (w : ↥C ⧸ GLAPPrimeCore 3 ↥C)
  rw [s1_barX_zpowers hbC] at h1
  have h2 : w ∈ Subgroup.zpowers
      (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩, hmem⟩ : ↥(barX 3 C L)) ↔
      (w : ↥C ⧸ GLAPPrimeCore 3 ↥C) ∈
        Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩) := by
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
  rw [h2, h1]
  constructor
  · intro h
    refine ⟨w.2, fun q hq => ?_⟩
    have := h ⟨q, hq⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨-, h⟩ g
    exact Subtype.ext (h g g.2).symm

private theorem s1_hn2 {C J L : Subgroup G} {b : G}
    (hbar : barX 3 C J = barX 3 C L)
    (hF : FusData (barX 3 C L) (barX 3 C (Subgroup.zpowers b))) :
    ∃ a ∈ J, a ^ 3 = 1 ∧ a ∉ Subgroup.zpowers b := by
  obtain ⟨a0, ha0Q, ha03, ha0Z⟩ := hF.exists_noncentral
  rw [← hbar] at ha0Q
  obtain ⟨c, hc, rfl⟩ := ha0Q
  have hcJ : (c : G) ∈ J := Subgroup.mem_subgroupOf.1 hc
  have hz : c ^ 3 ∈ GLAPPrimeCore 3 ↥C := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using ha03
  set m := orderOf (c ^ 3) with hm
  have hmc : m ∣ Nat.card (GLAPPrimeCore 3 ↥C) := by
    have := orderOf_dvd_natCard (⟨c ^ 3, hz⟩ : GLAPPrimeCore 3 ↥C)
    simpa using this
  have hm3 : m % 3 ≠ 0 := by
    intro h0
    have h3m : 3 ∣ m := Nat.dvd_of_mod_eq_zero h0
    have := (coprime_card_gLAPPrimeCore_aux 3 ↥C).eq_one_of_dvd (h3m.trans hmc)
    omega
  have hmm : m * m % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  obtain ⟨k, hk⟩ : ∃ k, m * m = 3 * k + 1 := ⟨m * m / 3, by omega⟩
  have ha3 : (c ^ (m * m)) ^ 3 = 1 := by
    have h1 : (c ^ 3) ^ m = 1 := pow_orderOf_eq_one _
    calc (c ^ (m * m)) ^ 3 = ((c ^ 3) ^ m) ^ m := by
          simp only [← pow_mul]; congr 1; ring
      _ = 1 := by rw [h1, one_pow]
  have himg : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (c ^ (m * m)) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) c := by
    rw [map_pow, hk, pow_succ, pow_mul, ha03, one_pow, one_mul]
  refine ⟨((c ^ (m * m) : ↥C) : G), Subgroup.mem_subgroupOf.1 (pow_mem hc _), ?_, ?_⟩
  · simpa using congrArg Subtype.val ha3
  · intro hz'
    apply ha0Z
    rw [← himg]
    exact ⟨c ^ (m * m), Subgroup.mem_subgroupOf.2 hz', rfl⟩

omit [Finite G] in
private theorem s1_layer_le {L X : Subgroup G} : GLAPLayer 3 (L ⊓ X) ≤ L ⊓ X :=
  sSup_le fun _ hK => hK.1

private theorem s1_b_mem {b : G} {L : Subgroup G} (hL : GLAPComponent 3 (Cb b) L)
    (hF : FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b))) (hb3 : b ^ 3 = 1) :
    b ∈ L := by
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hmem : mkX (Cb b) b hbC ∈ barX 3 (Cb b) (Subgroup.zpowers b) :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers b), rfl⟩
  exact q_mem_of_bar hL hbC (k := 1) (by simpa using hb3) (hF.Zle hmem)

private theorem s1_equiv {C J L : Subgroup G} (hJC : J ≤ C) (hLC : L ≤ C)
    (h : barX 3 C J = barX 3 C L) :
    ∃ e : (↥J ⧸ GLAPPrimeCore 3 ↥J) ≃* (↥L ⧸ GLAPPrimeCore 3 ↥L),
      ∀ g (hgJ : g ∈ J) (hgL : g ∈ L),
        e (QuotientGroup.mk ⟨g, hgJ⟩) = QuotientGroup.mk ⟨g, hgL⟩ := by
  obtain ⟨EJ, hEJ⟩ := s1_E hJC
  obtain ⟨EL, hEL⟩ := s1_E hLC
  obtain ⟨f, hf⟩ := s1_cast _ _ h
  refine ⟨(EJ.trans f).trans EL.symm, fun g hgJ hgL => ?_⟩
  have hgC : g ∈ C := hJC hgJ
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hEJ g hgJ hgC]
  rw [MulEquiv.symm_apply_eq, hEL g hgL hgC]
  exact hf _ _ _

theorem s1_core (i183 : Input18_3_4) (i145 : Input14_5) (i253 : Input25_3_27) {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    (hY : Y2 b L₂ L₃) {x : G} (hx : x ∈ L₃) (hx3 : x ^ 3 = 1) (hxb : x ∉ Subgroup.zpowers b) :
    b ∈ oPrimePOf 3 (Cb x) := by
  have hT := hR.tri
  have hb3' : b ^ 3 = 1 := hT.elemB.2 b hT.mem
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3' hT.ne_one
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hbL1 : b ∈ L₁ := s1_b_mem hT.comp₁ hR.fus₁ hb3'
  have hbL2 : b ∈ L₂ := s1_b_mem hT.comp₂ hR.fus₂ hb3'
  have hxC : x ∈ Cb b := hT.comp₃.1 hx
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ one_mem _)
  have hzx : Subgroup.zpowers x ≤ L₃ := Subgroup.zpowers_le.2 hx
  have hc1 : ⁅L₁, Subgroup.zpowers x⁆ ≤ P3 (Cb b) :=
    (Subgroup.commutator_mono le_rfl hzx).trans
      (commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₁ hT.comp₃ hT.ne₁₃)
  have hc2 : ⁅L₂, Subgroup.zpowers x⁆ ≤ P3 (Cb b) :=
    (Subgroup.commutator_mono le_rfl hzx).trans
      (commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₂ hT.comp₃ hT.ne₂₃)
  obtain ⟨hJ1c, hbJ1, hbar1, hJs1, hJJs1, hJ1c2⟩ :=
    jstar i183 hS hT.comp₁ hbL1 hb3' hR.fus₁ hxC hx3 hx1 hc1
  obtain ⟨hJ2c, hbJ2, hbar2, hJs2, hJJs2, hJ2c2⟩ :=
    jstar i183 hS hT.comp₂ hbL2 hb3' hR.fus₂ hxC hx3 hx1 hc2
  set J₁ := GLAPLayer 3 (L₁ ⊓ Cb x) with hJ₁
  set J₂ := GLAPLayer 3 (L₂ ⊓ Cb x) with hJ₂
  set Js₁ := ⨆ g ∈ GLAPLayer 3 (Cb x), GLBConj g J₁ with hJs₁
  set Js₂ := ⨆ g ∈ GLAPLayer 3 (Cb x), GLBConj g J₂ with hJs₂
  by_cases hJs : Js₁ = Js₂
  ·
    have h₂ : GLAPComponent 3 (Js₁ ⊓ Cb b) J₂ := by rw [hJs]; exact hJ2c2
    have hne : J₁ ≠ J₂ := by
      intro h
      apply hT.ne₁₂
      refine glaPComponent_uniqueAux hT.comp₁ hT.comp₂ ?_
      rw [← hbar1, ← hbar2, h]
    have hJ1L : J₁ ≤ L₁ := s1_layer_le.trans inf_le_left
    have hJ2L : J₂ ≤ L₂ := s1_layer_le.trans inf_le_left
    have hJ2x : J₂ ≤ Cb x := s1_layer_le.trans inf_le_right
    obtain ⟨e, he⟩ := s1_equiv (hJ1L.trans hT.comp₁.1) hT.comp₁.1 hbar1
    have hε₁ : IsSL3Eps (barOf 3 J₁) := s1_eps_of_equiv e.symm hR.eps₁
    have hZ₁ : Subgroup.center (barOf 3 J₁) =
        Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ1⟩ : ↥J₁)) := by
      refine s1_center_zpowers e _ ?_
      rw [he b hbJ1 hbL1]
      exact s1_center_barOf hT.comp₁ hbC hbL1 hR.fus₁
    have hn₂ : ∃ a ∈ J₂, a ^ 3 = 1 ∧ a ∉ Subgroup.zpowers b := s1_hn2 hbar2 hR.fus₂
    obtain ⟨y, hyJ2, hy3, hyb, hbny⟩ :=
      s1_tilde i145 i253 hS hbo hx1 hJs1 hJ1c2 h₂ hne hbJ1 hbJ2 hε₁ hZ₁ hn₂
    exfalso
    apply hbny
    have hyL2 : y ∈ L₂ := hJ2L hyJ2
    have hyCx : y ∈ Cb x := hJ2x hyJ2
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hyCx
    have hbyx := hY y hyL2 x hx hyx hy3 hx3 hyb hxb
    have hxCyx : x ∈ Cb (y * x) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * (y * x) = (x * y) * x := by group
        _ = (y * x) * x := by rw [hyx]
    have hbCx : b ∈ Cb x := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hxC).symm
    have h1 := o_inf_centralizer_le hxCyx ⟨1, by simpa using hx3⟩ ⟨hbyx, hbCx⟩
    have hW : Cb (y * x) ⊓ Cb x = Cb x ⊓ Cb y := by
      ext z
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        calc z * y = z * (y * x) * x⁻¹ := by group
          _ = (y * x) * z * x⁻¹ := by rw [h1]
          _ = y * (x * z) * x⁻¹ := by group
          _ = y * (z * x) * x⁻¹ := by rw [h2]
          _ = y * z := by group
      · rintro ⟨h2, h1⟩
        refine ⟨?_, h2⟩
        calc z * (y * x) = (z * y) * x := by group
          _ = (y * z) * x := by rw [h1]
          _ = y * (z * x) := by group
          _ = y * (x * z) := by rw [h2]
          _ = (y * x) * z := by group
    rw [hW] at h1
    have hsn := isSubnormal_inf hJs1.2.1 (Cb y)
    have hbyC : b ∈ Cb y := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hT.comp₂.1 hyL2)).symm
    exact o_inf_le_of_subnormal hsn ⟨h1, hJJs1 hbJ1, hbyC⟩
  ·
    have hb12 : b ∈ Js₁ ⊓ Js₂ := ⟨hJJs1 hbJ1, hJJs2 hbJ2⟩
    exact o_le_of_subnormal hJs1.2.1
      (inf_le_oPrimePOf_of_ne Nat.prime_three hJs1 hJs2 hJs hb12)

end S1Sec

section RMSec

omit [Finite G] in
private theorem rm_cb_conj (c w : G) :
    Cb (c * w * c⁻¹) = GLBConj c⁻¹ (Cb w) := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  simp only [inv_inv]
  constructor
  · intro h
    calc c⁻¹ * y * c * w = c⁻¹ * (y * (c * w * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * w * c⁻¹) * y) * c := by rw [h]
      _ = w * (c⁻¹ * y * c) := by group
  · intro h
    calc y * (c * w * c⁻¹) = c * ((c⁻¹ * y * c) * w) * c⁻¹ := by group
      _ = c * (w * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
      _ = c * w * c⁻¹ * y := by group

private theorem rm_transport {b c w : G} (hc : c * b = b * c) (h : b ∈ oPrimePOf 3 (Cb w)) :
    b ∈ oPrimePOf 3 (Cb (c * w * c⁻¹)) := by
  rw [rm_cb_conj, oPrimePOf_gLBConj, mem_gLBConj]
  have : c⁻¹ * b * c⁻¹⁻¹ = b := by
    rw [inv_inv]; calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
      _ = b := by rw [← hc]; group
  rwa [this]

omit [Finite G] in
private theorem rm_commute_of_B {B : Subgroup G} (hB : IsElemAbelian 3 B) {x y : G} (hx : x ∈ B)
    (hy : y ∈ B) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hB hx hy

private theorem rm_step {b β : G} {A A' : Subgroup G} (hβ : β * b = b * β)
    (hA : ∀ y, y ∈ A ↔ β * y * β⁻¹ ∈ A')
    (h : ∀ x ∈ A', x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x)) :
    ∀ x ∈ A, x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x) := by
  intro x hx hx3 hxn
  have hnz : ∀ x : G, β * x * β⁻¹ ∈ Subgroup.zpowers b → x ∈ Subgroup.zpowers b := by
    rintro x ⟨k, hk⟩
    have hcm : β * b ^ k = b ^ k * β := (Commute.zpow_right (show Commute β b from hβ) k).eq
    refine ⟨k, ?_⟩
    have hk' : β * x * β⁻¹ = b ^ k := hk.symm
    calc b ^ k = β⁻¹ * (β * b ^ k) := by group
      _ = β⁻¹ * (b ^ k * β) := by rw [hcm]
      _ = β⁻¹ * (β * x * β⁻¹) * β := by rw [hk']; group
      _ = x := by group
  have hmain := h (β * x * β⁻¹) ((hA x).1 hx) (by rw [conj_pow, hx3]; group)
    (fun h' => hxn (hnz x h'))
  have := rm_transport (b := b) (c := β⁻¹) (w := β * x * β⁻¹)
    (by simpa using (Commute.inv_left (show Commute β b from hβ)).eq) hmain
  have e : β⁻¹ * (β * x * β⁻¹) * β⁻¹⁻¹ = x := by group
  rwa [e] at this

private theorem rm_zp {b x : G} (hb : orderOf b = 3) (hx : x ∈ Subgroup.zpowers b)
    (hx3 : orderOf x = 3) : b ∈ oPrimePOf 3 (Cb x) := by
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := Subgroup.zpowers_le.2 hx
  have hEq : Subgroup.zpowers x = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hb, hx3]
  have hbx : b ∈ Subgroup.zpowers x := by rw [hEq]; exact Subgroup.mem_zpowers b
  have hbc : b ∈ Cb x := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨j, rfl⟩ := hbx
    exact ((Commute.refl x).zpow_left j).eq
  refine mem_oPrimePOf_of_forall_comm Nat.prime_three hbc fun y hy => ?_
  have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hy
  obtain ⟨j, hj⟩ := hbx
  rw [← hj]
  exact (((show Commute y x from hyx).zpow_right j).eq).symm

private theorem rm_b_mem {b : G} {L : Subgroup G} (hL : GLAPComponent 3 (Cb b) L)
    (hF : FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b))) (hb3 : b ^ 3 = 1) :
    b ∈ L := by
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hmem : mkX (Cb b) b hbC ∈ barX 3 (Cb b) (Subgroup.zpowers b) :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers b), rfl⟩
  exact q_mem_of_bar hL hbC (k := 1) (by simpa using hb3) (hF.Zle hmem)

theorem r_main (i183 : Input18_3_4) (i145 : Input14_5) (i253 : Input25_3_27) {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    (hY : Y2 b L₁ L₂) {Li Lj : Subgroup G} (hi : Li = L₁ ∨ Li = L₂ ∨ Li = L₃)
    (hj : Lj = L₁ ∨ Lj = L₂ ∨ Lj = L₃) {x : G} (hx : x ∈ Li ⊔ Lj) (hx3 : orderOf x = 3) :
    b ∈ oPrimePOf 3 (Cb x) := by
  have hT := hR.tri
  have hb3' : b ^ 3 = 1 := hT.elemB.2 b hT.mem
  have hbo : orderOf b = 3 :=
    orderOf_eq_prime hb3' hT.ne_one
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨β, hβB, h21, h32, h13⟩ := hT.cyc
  have hβb : β * b = b * β := rm_commute_of_B hT.elemB hβB hT.mem
  have hm : ∀ {X Y : Subgroup G}, X = GLBConj β Y → ∀ y, y ∈ X ↔ β * y * β⁻¹ ∈ Y := by
    intro X Y hXY y
    rw [hXY, mem_gLBConj]
  have hY23 := (y2_cyc hT hY).1
  have hY31 := (y2_cyc hT hY).2
  have hY21 := y2_symm hY
  have hY32 := y2_symm hY23
  have hY13 := y2_symm hY31
  have hP3 : ∀ x ∈ L₃, x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x) :=
    fun x hx hx3 hxb => s1_core i183 i145 i253 hS hR hY23 hx hx3 hxb
  have hP1 : ∀ x ∈ L₁, x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x) :=
    rm_step hβb (hm h13) hP3
  have hP2 : ∀ x ∈ L₂, x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x) :=
    rm_step hβb (hm h21) hP1
  have hF : ∀ {L : Subgroup G}, (L = L₁ ∨ L = L₂ ∨ L = L₃) →
      (∀ x ∈ L, x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x)) ∧
        GLAPComponent 3 (Cb b) L ∧
        FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b)) := by
    intro L hL
    rcases hL with rfl | rfl | rfl
    · exact ⟨hP1, hT.comp₁, hR.fus₁⟩
    · exact ⟨hP2, hT.comp₂, hR.fus₂⟩
    · exact ⟨hP3, hT.comp₃, hR.fus₃⟩
  have hfull : ∀ {L : Subgroup G}, (L = L₁ ∨ L = L₂ ∨ L = L₃) → ∀ y ∈ L, orderOf y = 3 →
      b ∈ oPrimePOf 3 (Cb y) := by
    intro L hL y hy hy3
    by_cases hz : y ∈ Subgroup.zpowers b
    · exact rm_zp hbo hz hy3
    · exact (hF hL).1 y hy (by rw [← hy3]; exact pow_orderOf_eq_one y) hz
  have hbmem : ∀ {L : Subgroup G}, (L = L₁ ∨ L = L₂ ∨ L = L₃) → b ∈ L := fun hL =>
    rm_b_mem (hF hL).2.1 (hF hL).2.2 hb3'
  by_cases hij : Li = Lj
  · subst hij
    rw [sup_idem] at hx
    exact hfull hi x hx hx3
  have hxc : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hYij : Y2 b Li Lj := by
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      first | exact absurd rfl hij | assumption
  obtain ⟨c, hc, u, hu, v, hv, hcm, hu3, hv3, hcx⟩ :=
    decomp_sylow (hF hi).2.1 (hF hj).2.1 hij (hF hi).2.2 (hF hj).2.2 hx hxc
  have hcC : c ∈ Cb b := by
    have : Li ⊔ Lj ≤ Cb b := sup_le (hF hi).2.1.1 (hF hj).2.1.1
    exact this hc
  have hcb : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  have hord : orderOf (u * v) = 3 := by
    rw [← hcx, ← hx3]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
  suffices h : b ∈ oPrimePOf 3 (Cb (u * v)) by
    have h2 := rm_transport (b := b) (c := c⁻¹) (w := u * v)
      (by simpa using (Commute.inv_left (show Commute c b from hcb)).eq) h
    rw [← hcx] at h2
    have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rwa [e] at h2
  by_cases huz : u ∈ Subgroup.zpowers b
  · have : u * v ∈ Lj := mul_mem
      ((Subgroup.zpowers_le.2 (hbmem hj)) huz) hv
    exact hfull hj _ this hord
  by_cases hvz : v ∈ Subgroup.zpowers b
  · have : u * v ∈ Li := mul_mem hu ((Subgroup.zpowers_le.2 (hbmem hi)) hvz)
    exact hfull hi _ this hord
  exact hYij u hu v hv hcm hu3 hv3 huz hvz

end RMSec

theorem lemma27a_of_inputs (h25 : Lemma25Strong) (i112 : Input11_2Full)
    (i112f : Input11_2Four) (i302 : Input30_2) (i183 : Input18_3_4) (i145 : Input14_5)
    (i253 : Input25_3_27) : Lemma27a := by
  intro G _ _ m hS B hB b hbB hb1 L hL hn hbK hA Li Lj hLi hLj x hx hx3
  obtain ⟨D, hset, hconc, hZ⟩ := hA
  have hB1 : IsBOneMax 3 B := CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax
    (by norm_num) hB
  obtain ⟨L₂, L₃, hT, hK, hall⟩ := exists_tri i112 hS hB1 hbB hb1 hL hn
  have htype : IsSLThree (barOf 3 L) ∨ IsSUThree (barOf 3 L) := by
    rcases hconc.2.1 with ⟨K, hF, hfin, -, he⟩ | ⟨K, hF, hfin, q, hq, -, he⟩
    · exact Or.inl ⟨K, hF, hfin, he⟩
    · exact Or.inr ⟨K, hF, hfin, q, hq, he⟩
  have hR := rData_of_inputs i112f i302 hS hB1 hT hK hbK hZ htype
  obtain ⟨u, hu, v, hv, hc, hu3, hv3, hnu, hnv, hgood⟩ := case_a_good h25 hS hR hset hconc hZ
  have hY := y2_of_exists hR hu hv hc hu3 hv3 hnu hnv hgood
  exact r_main i183 i145 i253 hS hR hY (hall Li hLi) (hall Lj hLj) hx hx3

theorem lemma27b_of_inputs (i112 : Input11_2Full) (i112f : Input11_2Four) (i112t : Input11_2Two)
    (iB0 : InputB0T) (i302 : Input30_2) (i183 : Input18_3_4) (i145 : Input14_5)
    (i253 : Input25_3_27) (i1433 : Input14_33) (iD4 : InputD4) : Lemma27b := by
  intro G _ _ m hS B hB b hbB hb1 L hL hn hbK hbd Li Lj hLi hLj x hx hx3
  obtain ⟨hrk4, htype, -, hwb⟩ := hbd
  have hB1 : IsBOneMax 3 B := CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax
    (by norm_num) hB
  obtain ⟨L₂, L₃, hT, hK, hall⟩ := exists_tri i112 hS hB1 hbB hb1 hL hn
  have hX3 := exists_noncentral_of_four i112f hS hB1 hT hK hbK
  by_cases hZ : barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L)
  · have hR := rData_of_inputs i112f i302 hS hB1 hT hK hbK hZ htype
    have hY : Y2 b L L₂ := by
      by_contra hnY
      exact b_final i112t iB0 hS hrk4 hB hwb hT hK hbK hX3
        (b1_rank5 i183 i145 i302 i1433 iD4 hS hrk4 hR hK hbK hnY)
    exact r_main i183 i145 i253 hS hR hY (hall Li hLi) (hall Lj hLj) hx hx3
  · exact (b_final i112t iB0 hS hrk4 hB hwb hT hK hbK hX3
      (b2_rank5 i112 i112f hS hB1 hT hK hbK hZ)).elim


end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.NarrowI253

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  Lemma27Ns
open scoped Matrix commutatorElement

theorem lemma27_of_inputs_no38 (_h24 : Lemma24) (h25 : Lemma25Strong) (i112 : Input11_2Full)
    (i112f : Input11_2Four) (i112t : Input11_2Two) (iB0 : InputB0T) (i302 : Input30_2)
    (i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4) (i145 : Input14_5)
    (i253 : Input25_3_27) (i1433 : Input14_33)
    (iD4 : InputD4) : Lemma27 := by
  intro G _ _ m hS B hB b hb hb1 L hL hn hbK hcase Li Lj hLi hLj x hx hx3
  rcases hcase with hA | hb'
  · exact NarrowI253.lemma27a_of_inputs h25 i112 i112f i302 i183 i145 i253 G m hS B hB b hb hb1 L hL hn hbK
      hA Li Lj hLi hLj x hx hx3
  · exact NarrowI253.lemma27b_of_inputs i112 i112f i112t iB0 i302 i183 i145 i253 i1433 iD4 G m hS B hB b hb
      hb1 L hL hn hbK hb' Li Lj hLi hLj x hx hx3


namespace Lemma512Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

theorem lemma512_aux_no38 (h510 : Lemma510) (i183 : Input18_3) (i253 : Input25_3_512)
    (iFix : InputSL3FieldFixed) (iRes : InputSL3FieldRestrict) : Lemma512 := by
  intro G _ _ m hS h4 B hB b hb hb1 L hL hbL A hA hbA x hxb hx3 hxA hfld
  have hBe : CFSG.Open.IsElemAbelian 3 B := hB.1.1
  have hb3 : b ^ 3 = 1 := hBe.2 b hb
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hbx : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 hxb
  have hLb : L ≤ Cen b := hL.1.1
  have hbZ : ∀ l ∈ L, l * b = b * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hLb hl)
  have hAB : A ≤ B := hA.1
  have hxmem : x ∈ A ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hgN : ∀ g ∈ A ⊔ Subgroup.zpowers x, g ∈ Subgroup.normalizer (L : Set G) :=
    fun g hg => (hfld g hg).1
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hgN x hxmem
  have hAC : A ≤ Cen x := fun a ha => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hxA) a ha
  obtain ⟨hty, -, hiv⟩ := h510 G m hS h4 B hB b hb hb1 L hL
  have hbL1 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨b, hbL⟩ : barOf 3 L) ≠ 1 := by
    intro h
    have := orderOf_mk_prime_three hbL hbo
    rw [h, orderOf_one] at this
    omega
  have : Nontrivial (barOf 3 L) := ⟨⟨_, 1, hbL1⟩⟩
  have hLq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_barOf Nat.prime_three hL.1 inferInstance
  have hbcen : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨b, hbL⟩ : barOf 3 L) ∈
      Subgroup.center (barOf 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hbZ l l.2)
  have hα3 : (barAut 3 L ⟨x, hxN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext hx3'
    rw [this, map_one]
  have hαf : IsFieldAutThree (barAut 3 L ⟨x, hxN⟩) := (hfld x hxmem).2
  set E : Subgroup (MulAut (barOf 3 L)) :=
    ((A ⊔ Subgroup.zpowers x).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L)
    with hE
  have hαE : barAut 3 L ⟨x, hxN⟩ ∈ E :=
    ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.2 hxmem, rfl⟩
  have hEf : ∀ ε ∈ E, IsFieldAutThree ε := by
    rintro ε ⟨γ, hγ, rfl⟩
    exact (hfld γ.1 (Subgroup.mem_subgroupOf.1 hγ)).2
  obtain ⟨hFq, hFt⟩ := iFix (barOf 3 L) hLq hty ⟨_, hbcen, hbL1⟩ _ hα3 hαf
  have hres := iRes (barOf 3 L) hLq hty ⟨_, hbcen, hbL1⟩ _ hα3 hαf
  have hfix := fixedSub_barAut_eq hx3' hxN
  rw [hfix] at hFq hFt hres
  have hZ : Nat.card (Subgroup.center ↥(barX 3 L (L ⊓ Cen x))) = 3 :=
    card_center_of_isSLThreeEpsAny hFt
  obtain ⟨J₀, hJ0c, hJ0top, hJ0F, hJ0N⟩ := exists_J0 hFq hZ
  rw [← hJ0F] at hFq hFt hres hZ
  have hbH : b ∈ L ⊓ Cen x :=
    ⟨hbL, Subgroup.mem_centralizer_singleton_iff.2 hbx.symm⟩
  have hbJ0 : b ∈ J₀ :=
    mem_of_barX_eq_top hJ0top hbH hb3 (fun h hh => (hbZ h hh.1).symm)
  have hLle : L ≤ GLAPLayer 3 (Cen b) := le_sSup hL.1
  have hLayer_le : ∀ X : Subgroup G, GLAPLayer 3 X ≤ X := fun X => sSup_le fun K hK => hK.1
  have hLsn : CFSG.Open.IsSubnormal L (GLAPLayer 3 (Cen b)) :=
    isSubnormal_of_le_of_le hL.1.2.1 hLle (hLayer_le _)
  have hHsnM : CFSG.Open.IsSubnormal (L ⊓ Cen x) (GLAPLayer 3 (Cen b) ⊓ Cen x) :=
    isSubnormal_inf hLsn (Cen x)
  have hJ0snM : CFSG.Open.IsSubnormal J₀ (GLAPLayer 3 (Cen b) ⊓ Cen x) :=
    isSubnormal_trans' hJ0c.2.1 hHsnM
  have hJ0M : GLAPComponent 3 (GLAPLayer 3 (Cen b) ⊓ Cen x) J₀ :=
    glaPComponent_up Nat.prime_three hJ0c (inf_le_inf_right _ hLle) hJ0snM
  have hJ0Mle : J₀ ≤ GLAPLayer 3 (GLAPLayer 3 (Cen b) ⊓ Cen x) := le_sSup hJ0M
  have hJ0Ml : GLAPComponent 3 (GLAPLayer 3 (GLAPLayer 3 (Cen b) ⊓ Cen x)) J₀ :=
    glaPComponent_down Nat.prime_three hJ0M hJ0Mle (hLayer_le _)
  have := hS.simple
  obtain ⟨hdich, h3⟩ := i183 G hS.nonabelian hS.kProper b x hbo hx3 hbx.symm J₀ hJ0Ml
  have hbC : b ∈ Cen x := Subgroup.mem_centralizer_singleton_iff.2 hbx.symm
  have hJK : J₀ ≤ conjHull x J₀ := by
    have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Cen x)) => GLBConj g J₀) 1 (one_mem _)
    rwa [gLBConj_one] at this
  obtain ⟨L₁, hL₁, hK⟩ : ∃ L₁ : Subgroup G, GLAPComponent 3 (Cen x) L₁ ∧ conjHull x J₀ = L₁ := by
    rcases hdich with ⟨L₁, hL₁, hK, -⟩ | ⟨L₁, L₂, L₃, h₁, h₂, h₃, h12, h23, h31, hu1, -, -, hK⟩
    · exact ⟨L₁, hL₁, hK⟩
    · exact (not_diag hbJ0 (hK ▸ hJK) h₁ h₂ h₃ h12 h31 hu1).elim
  have hJ0L : J₀ ≤ L := fun j hj => (hJ0c.1 hj).1
  have hJ0C : J₀ ≤ Cen x := fun j hj => (hJ0c.1 hj).2
  have hCne : Cen x ≠ ⊤ := by
    intro htop
    have hxc : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Cen x := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    have hnorm : (Subgroup.center G).Normal := inferInstance
    rcases hS.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h] at hxc
      have : x = 1 := hxc
      rw [this, orderOf_one] at hx3
      omega
    · obtain ⟨a, c, hac⟩ := hS.nonabelian
      have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
      exact hac ((Subgroup.mem_center_iff.1 ha) c).symm
  have hKgrpC : CFSG.Open.IsKGroup ↥(Cen x) := isKGroup_of_isKProper hS.kProper hCne
  have hKC : conjHull x J₀ ≤ Cen x := hK ▸ hL₁.1
  have hKq : CFSG.Open.IsQuasisimple ↥(barX 3 (Cen x) (conjHull x J₀)) := by
    rw [hK]; exact hL₁.2.2.1.2.2
  have hKsn : CFSG.Open.IsSubnormal (barX 3 (Cen x) (conjHull x J₀)) ⊤ := by
    rw [hK]; exact hL₁.2.2.1.2.1
  have hKg : CFSG.Open.IsKGroup ↥(barX 3 (Cen x) (conjHull x J₀)) :=
    isKGroup_subgroup_quotient hKgrpC (GLAPPrimeCore 3 ↥(Cen x)) _
  have hKcore : GLAPPrimeCore 3 ↥(barX 3 (Cen x) (conjHull x J₀)) = ⊥ :=
    glaPPrimeCore_eq_bot_of_isSubnormal (glaPPrimeCore_quotient_eq_bot Nat.prime_three) hKsn
  have hbK : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩) ∈
      barX 3 (Cen x) (conjHull x J₀) :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 (hJK hbJ0), rfl⟩
  have hbJ' : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩) ∈
      barX 3 (Cen x) J₀ := ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hbJ0, rfl⟩
  have hbo' : orderOf (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩) = 3 :=
    orderOf_mk_prime_three hbC hbo
  have hJcomp := h3 hbC
  have hAcomm : ∀ a ∈ A, a * x = x * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.1 (hAC ha)
  have hAnorm : A ≤ Subgroup.normalizer (conjHull x J₀ : Set G) :=
    le_normalizer_conjHull hAC fun a ha =>
      hJ0N a (hgN a (Subgroup.mem_sup_left ha)) (hAcomm a ha)
  have hAel := barX_card_elemAbelian hAC hA.2.1
  have hAcard : Nat.card (barX 3 (Cen x) A) = 9 := by
    rw [hAel.2, hA.2.2]; norm_num
  have hAnorm' : barX 3 (Cen x) A ≤
      Subgroup.normalizer (barX 3 (Cen x) (conjHull x J₀) : Set (CBarOf x)) :=
    barX_le_normalizer hAnorm
  have hbA' : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩) ∈ barX 3 (Cen x) A :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hbA, rfl⟩
  have hF0 : GLAPPrimeCore 3 ↥(barX 3 L J₀) = ⊥ := glaPPrimeCore_eq_bot_of_quasisimple hFq hZ
  obtain ⟨e, he1, he2⟩ := exists_equiv_barOf_barX hJ0L hJ0C hF0
  have hFt' : IsSLThreeEpsAny ↥(barX 3 L J₀) := hFt
  have ha' : IsSLThreeEpsAny (barOf 3 (barX 3 (Cen x) J₀)) := isSLThreeEpsAny_congr e.symm hFt'
  have hb' : Subgroup.center (barOf 3 (barX 3 (Cen x) J₀)) =
      Subgroup.zpowers (QuotientGroup.mk (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x))
        ⟨b, hbC⟩, hbJ'⟩ : ↥(barX 3 (Cen x) J₀))) := by
    have hcard : Nat.card (Subgroup.center (barOf 3 (barX 3 (Cen x) J₀))) = 3 := by
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact hZ
    have hmem : ((QuotientGroup.mk (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x))
        ⟨b, hbC⟩, hbJ'⟩ : ↥(barX 3 (Cen x) J₀)) : barOf 3 (barX 3 (Cen x) J₀))) ∈
        Subgroup.center (barOf 3 (barX 3 (Cen x) J₀)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨⟨j, hjC⟩, hj, hjw⟩ := w.2
      have hj' : j ∈ J₀ := Subgroup.mem_subgroupOf.1 hj
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show (w : CBarOf x) * QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩ * (w : CBarOf x)
      rw [← hjw, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hbZ j (hJ0L hj'))
    have hne : ((QuotientGroup.mk (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x))
        ⟨b, hbC⟩, hbJ'⟩ : ↥(barX 3 (Cen x) J₀)) : barOf 3 (barX 3 (Cen x) J₀))) ≠ 1 := by
      intro h
      have := he1 b hbJ0
      rw [h, map_one] at this
      exact hbL1 this.symm
    exact center_eq_zpowers_of_card_three hcard hmem hne
  have hc' : ∀ a ∈ barX 3 (Cen x) A, a ≠ 1 → InducesFieldAut 3 (barX 3 (Cen x) J₀) a := by
    rintro _ ⟨⟨a, haC⟩, ha, rfl⟩ -
    have haA : a ∈ A := Subgroup.mem_subgroupOf.1 ha
    have haE : barAut 3 L ⟨a, hgN a (Subgroup.mem_sup_left haA)⟩ ∈ E :=
      ⟨⟨a, hgN a (Subgroup.mem_sup_left haA)⟩,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left haA), rfl⟩
    obtain ⟨ρ, hρ, hρf⟩ := hres E hαE hEf _ haE
    exact (he2 a haC (hgN a (Subgroup.mem_sup_left haA))
      (hJ0N a (hgN a (Subgroup.mem_sup_left haA)) (hAcomm a haA)) ρ hρ hρf)
  have hmain := i253 (CBarOf x) (barX 3 (Cen x) (conjHull x J₀)) (barX 3 (Cen x) J₀)
    (barX 3 (Cen x) A) _ hbJ' hKq hKg hKcore hbK hbo' hJcomp ha' hb' hAnorm' hAel.1 hAcard hbA'
    hc' (i253_su38Trivial_512 hLq hty ⟨_, hbcen, hbL1⟩ hx3' hxN
      (fun a ha => hBe.2 a (hAB ha)) hAC hfld hJ0L hJ0C
      (by rw [fixedSub_barAut_eq hx3' hxN, hJ0F])
      (fun a ha => hJ0N a (hgN a (Subgroup.mem_sup_left ha)) (hAcomm a ha)) e he1)
  rcases hmain with hJK' | ⟨ã, hã, hã1, hnot⟩
  ·
    have hz := comm_mem_core_of_barX hKC hJK'.symm.le hbC
      (fun j hj => hbZ j (hJ0L hj))
    exact mem_oPrimePOf_of_central_subnormal (hK ▸ hL₁.2.1) (hJK hbJ0) hb3 hz
  ·
    exfalso
    obtain ⟨⟨a, haC⟩, ha, rfl⟩ := hã
    have haA : a ∈ A := Subgroup.mem_subgroupOf.1 ha
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hã1 (by
        show QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨1, haC⟩ = 1
        exact map_one _)
    have ha3 : a ^ 3 = 1 := hBe.2 a (hAB haA)
    have hbCa : b ∈ oPrimePOf 3 (Cen a) := by
      have h4 := (hiv a (hAB haA) ha1 (hfld a (Subgroup.mem_sup_left haA))).2.2
      exact h4 ⟨hb, mem_oPrimePOf_of_forall_comm Nat.prime_three hbL
        (fun y hy => (hbZ y hy).symm)⟩
    exact hnot (mem_oPrimePOf_barX hKC haC ha3 (hAnorm haA) (hJK hbJ0) hbC hbCa)



end Lemma512Ns

theorem lemma512_of_inputs_no38 (h510 : Lemma510) (i183 : Lemma512Ns.Input18_3)
    (i253 : Input25_3_512) (iFix : Lemma512Ns.InputSL3FieldFixed)
    (iRes : Lemma512Ns.InputSL3FieldRestrict) : Lemma512 :=
  Lemma512Ns.lemma512_aux_no38 h510 i183 i253 iFix iRes

end CFSG.HardMathSupport.Solomon.LocalBalance
