module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive
public import CFSG.Quasithin.Background.C124FStar
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreNineD
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.B1Red CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.Coordinator
open scoped commutatorElement

section Aux

variable {G : Type*} [Group G]

theorem exists_mul_of_sup {L A : Subgroup G} (hA : A ≤ Subgroup.normalizer (L : Set G))
    {g : G} (hg : g ∈ L ⊔ A) : ∃ l ∈ L, ∃ a ∈ A, g = l * a := by
  have hL : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  set N := Subgroup.normalizer (L : Set G)
  have hsup : L ⊔ A ≤ N := sup_le hL hA
  have hg' : (⟨g, hsup hg⟩ : N) ∈ L.subgroupOf N ⊔ A.subgroupOf N := by
    rw [← Subgroup.subgroupOf_sup hL hA]
    exact hg
  have : (L.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg'
  obtain ⟨l, hl, a, ha, h⟩ := hg'
  exact ⟨l, hl, a, ha, congrArg Subtype.val h.symm⟩

end Aux


section Alt

variable {G : Type*} [Group G]

theorem isQuasisimple_of_alt {n : ℕ} (hn : 5 ≤ n) (e : G ≃* alternatingGroup (Fin n)) :
    CFSG.Open.IsQuasisimple G := by
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn)
  have : IsSimpleGroup G := MulEquiv.isSimpleGroup e
  have hZ : Subgroup.center G = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have h4 : 4 ≤ Nat.card (Fin n) := by rw [Nat.card_fin]; omega
    have hc : e g ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff] at hg ⊢
      intro y
      have := congrArg e (hg (e.symm y))
      simpa using this
    rw [alternatingGroup.center_eq_bot h4, Subgroup.mem_bot] at hc
    exact e.injective (by simpa using hc)
  refine ⟨?_, ?_⟩
  · have hnorm : (commutator G).Normal := inferInstance
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ _ (commutator G) hnorm with h | h
    · exfalso
      have hcomm : ∀ a b : G, a * b = b * a := by
        intro a b
        have : ⁅a, b⁆ ∈ commutator G := by
          rw [commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot] at this
        exact commutatorElement_eq_one_iff_mul_comm.1 this
      have : Subgroup.center G = ⊤ := by
        rw [eq_top_iff]
        intro g _
        exact Subgroup.mem_center_iff.2 fun y => hcomm y g
      obtain ⟨x, hx⟩ := exists_ne (1 : G)
      have hxc : x ∈ Subgroup.center G := by rw [this]; trivial
      rw [hZ, Subgroup.mem_bot] at hxc
      exact hx hxc
    · exact h
  · have e' : (G ⧸ Subgroup.center G) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact MulEquiv.isSimpleGroup e'

theorem alt_not_two_group {n : ℕ} (hn : 3 ≤ n) : ¬ IsPGroup 2 (alternatingGroup (Fin n)) := by
  intro h
  set a : Fin n := ⟨0, by omega⟩
  set b : Fin n := ⟨1, by omega⟩
  set c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have h3 : (Equiv.swap a b * Equiv.swap a c).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hm : (Equiv.swap a b * Equiv.swap a c) ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup]; exact h3.sign
  obtain ⟨k, hk⟩ := h ⟨_, hm⟩
  have h1 : orderOf ((⟨_, hm⟩ : alternatingGroup (Fin n))) = 3 := by
    rw [← Subgroup.orderOf_coe]; exact h3.orderOf
  have h2 : orderOf ((⟨_, hm⟩ : alternatingGroup (Fin n))) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  rw [h1] at h2
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
  omega

end Alt


section Main

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def natU (H : Subgroup (MulAut V)) : Subgroup V :=
  (commV (autSub H (fixV (pCoreOf 2 H)))).map (fixV (pCoreOf 2 H)).subtype

theorem natural_on_fixV (hGF : GF2EightFive) (hV : ∀ v : V, v ^ 2 = 1)
    {H L A : Subgroup (MulAut V)} {n : ℕ} (hn : 9 ≤ n) (e : ↥L ≃* alternatingGroup (Fin n))
    (hLH : L ≤ H) (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) (hHA : H ≤ L ⊔ A)
    (hoff : IsFFStarOffender H A) (hAL : ¬ ∀ a ∈ A, ∀ l ∈ L, a * l = l * a) :
    ∃ α : ↥L →* alternatingGroup (Fin n), Function.Surjective α ∧
      ∃ π : ↥(natU H) →* Multiplicative (altHeart n),
        (∀ u, π u = 1 → ∀ l ∈ L, l (u : V) = u) ∧
        ∀ (l : ↥L) (u v : ↥(natU H)), (v : V) = (l : MulAut V) (u : V) → ∀ x : evenWeight n,
          Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
          Multiplicative.toAdd (π v) =
            (QuotientAddGroup.mk (evenWeightPerm (α l : Equiv.Perm (Fin n)) x) : altHeart n) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 H with hPdef
  set W := fixV P with hWdef
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hPH : P ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hAH : A ≤ H := hoff.1
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hoff.2.2.1.2
  have hsimple : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
    exact MulEquiv.isSimpleGroup e
  have hLP1 : L ⊓ P = ⊥ := by
    have hnorm : ((L ⊓ P).subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff inf_le_left).2 fun y l hy hl =>
        ⟨L.mul_mem (L.mul_mem hl hy.1) (L.inv_mem hl), conj_mem_pCoreOf (hLH hl) hy.2⟩
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥L _ _ _ hnorm with h | h
    · refine eq_bot_iff.2 fun x hx => ?_
      have hx' : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ P).subgroupOf L := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx')
    · exfalso
      have hLP : L ≤ P := fun x hx => by
        have hx' : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ P).subgroupOf L := by rw [h]; trivial
        exact hx'.2
      have h2 : IsPGroup 2 ↥L := hP2.to_le hLP
      exact alt_not_two_group (by omega) (h2.of_surjective e.toMonoidHom e.surjective)
  have hLP : ∀ x ∈ L, ∀ q ∈ P, x * q = q * x := by
    intro x hx q hq
    have h1 : x * q * x⁻¹ * q⁻¹ ∈ L := by
      have := L.mul_mem hx (hLn q (hPH hq) x⁻¹ (L.inv_mem hx))
      simpa [mul_assoc] using this
    have h2 : x * q * x⁻¹ * q⁻¹ ∈ P :=
      P.mul_mem (conj_mem_pCoreOf (hLH hx) hq) (P.inv_mem hq)
    have h3 : x * q * x⁻¹ * q⁻¹ ∈ L ⊓ P := ⟨h1, h2⟩
    rw [hLP1, Subgroup.mem_bot] at h3
    calc x * q = (x * q * x⁻¹ * q⁻¹) * q * x := by group
      _ = q * x := by rw [h3]; group
  have hAn : A ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    le_normalizer_of_conj fun a ha l hl => hLn a (hAH ha) l hl
  have hsq : ∀ x ∈ H, x ^ 2 ∈ L := by
    intro x hx
    obtain ⟨l, hl, a, ha, rfl⟩ := exists_mul_of_sup hAn (hHA hx)
    have ha1 : a * a = 1 := by simpa [pow_two] using hA2 a ha
    have : (l * a) ^ 2 = l * (a * l * a⁻¹) * (a * a) := by rw [pow_two]; simp [mul_assoc]
    rw [this, ha1, mul_one]
    exact L.mul_mem hl (hLn a (hAH ha) l hl)
  have hD : ∀ x ∈ H, Odd (orderOf x) → x ∈ L := by
    intro x hx ho
    obtain ⟨m, hm⟩ := ho
    have hx1 : x ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one x
    have : (x ^ 2) ^ (m + 1) = x := by
      rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hx1, one_mul]
    exact this ▸ L.pow_mem (hsq x hx) (m + 1)
  have hker : H ⊓ centSub W = P := kernel_eq_pCoreOf hV hD hLP
  have hO2 : pCoreOf 2 (autSub H W) = ⊥ := pCoreOf_autSub_eq_bot hker
  have hHst : H ≤ stabSub W := le_stabSub_fixV_pCoreOf H
  have hLst : L ≤ stabSub W := hLH.trans hHst
  let fL : ↥L →* MulAut ↥W := (resHom W).comp (Subgroup.inclusion hLst)
  have hfL_mem : ∀ l, fL l ∈ autSub L W := fun l => mem_autSub.2 ⟨⟨l, hLst l.2⟩, l.2, rfl⟩
  let φ : ↥L →* ↥(autSub L W) := fL.codRestrict _ hfL_mem
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : fL l = 1 := congrArg Subtype.val hl
    have h2 : (⟨(l : MulAut V), hLst l.2⟩ : stabSub W) ∈ (resHom W).ker := h1
    rw [ker_resHom, Subgroup.mem_subgroupOf] at h2
    have h3 : (l : MulAut V) ∈ H ⊓ centSub W := ⟨hLH l.2, h2⟩
    rw [hker] at h3
    have h4 : (l : MulAut V) ∈ L ⊓ P := ⟨l.2, h3⟩
    rw [hLP1, Subgroup.mem_bot] at h4
    exact Subtype.ext h4
  have hφsurj : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hgL, hg⟩ := mem_autSub.1 hψ
    exact ⟨⟨g.1, hgL⟩, Subtype.ext hg⟩
  let eL : ↥L ≃* ↥(autSub L W) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let eLb : ↥(autSub L W) ≃* alternatingGroup (Fin n) := eL.symm.trans e
  have hq : CFSG.Open.IsQuasisimple ↥(autSub L W) := isQuasisimple_of_alt (by omega) eLb
  have hconj : ∀ y ∈ autSub H W, ∀ l ∈ autSub L W, y * l * y⁻¹ ∈ autSub L W :=
    fun y hy l hl => autSub_conj_mem (fun x hx y hy => hLn x hx y hy) hy hl
  have h2 : ∀ y ∈ autSub H W, ∃ k : ℕ, y ^ 2 ^ k ∈ autSub L W := by
    intro y hy
    obtain ⟨g, hgH, rfl⟩ := mem_autSub.1 hy
    refine ⟨1, mem_autSub.2 ⟨g ^ 2, ?_, ?_⟩⟩
    · exact hsq _ hgH
    · simp [map_pow]
  have hFstar : quasithinGenFitting (autSub H W) = autSub L W :=
    C124.quasithinGenFitting_eq_of_two_group_quot (autSub_mono hLH W) hconj (Or.inl hq) h2 hO2
  have hWA : commSub W A ≠ ⊥ := by
    intro h
    rw [commSub_eq_bot_iff] at h
    apply hAL
    intro a ha l hl
    have h1 : a ∈ H ⊓ centSub W := ⟨hAH ha, fun w hw => h hw a ha⟩
    rw [hker] at h1
    exact (hLP l hl a h1).symm
  have hoff' : IsFFStarOffender (autSub H W) (autSub A W) :=
    B7_1_1 hoff (fun a ha w hw => fixV_pCoreOf_inv a (hAH ha) w hw) hWA
  have hW2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (hV v)
  have hnat := hGF ↥W hW2 (autSub H W) (autSub L W) hFstar.symm n (Or.inr hn) ⟨eLb⟩
    ⟨_, hoff'⟩
  rcases hnat with ⟨α', hα', π', hπ's, hπ'ker, hπ'eq⟩ | ⟨h7, -⟩
  swap
  · omega
  let eU : ↥(commV (autSub H W)) ≃* ↥(natU H) :=
    Subgroup.equivMapOfInjective _ W.subtype W.subtype_injective
  have hcoe : ∀ y : ↥(commV (autSub H W)), ((eU y : ↥(natU H)) : V) = (((y : ↥W)) : V) := fun y => rfl
  refine ⟨α'.comp φ, hα'.comp hφsurj, π'.comp eU.symm.toMonoidHom, ?_, ?_⟩
  · intro u hu l hl
    have h1 : eU.symm u ∈ π'.ker := hu
    rw [hπ'ker, Subgroup.mem_subgroupOf] at h1
    have h2 := (mem_fixV_autSub.1 h1.2) l hl (hLst hl)
    have h3 : (u : V) = (((eU.symm u : ↥(commV (autSub H W))) : ↥W) : V) := by
      have := hcoe (eU.symm u)
      simpa using this
    rw [h3]
    exact h2
  · intro l u v hv x hx
    have h3 : ∀ w : ↥(natU H), (w : V) = (((eU.symm w : ↥(commV (autSub H W))) : ↥W) : V) := by
      intro w
      have := hcoe (eU.symm w)
      simpa using this
    refine hπ'eq (φ l) (eU.symm u) (eU.symm v) ?_ x hx
    apply Subtype.ext
    show (((eU.symm v : ↥(commV (autSub H W))) : ↥W) : V) = (l : MulAut V) (((eU.symm u : ↥(commV (autSub H W))) : ↥W) : V)
    rw [← h3, ← h3]
    exact hv

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
