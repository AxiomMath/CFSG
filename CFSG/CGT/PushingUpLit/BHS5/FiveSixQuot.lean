module

public import CFSG.CGT.PushingUpLit.BHS5.QuotAct
public import CFSG.CGT.PushingUpLit.BHS5.ThreeFour
public import CFSG.CGT.PushingUpLit.BHS.AltCore
public import CFSG.CGT.PushingUpLit.BHS.ThreeSixD

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.CGT.PushingUpLit.BHS

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def fixOp (P : Subgroup (MulAut V)) : Subgroup V := fixV (opResidual 2 P)

omit [Finite V] in
theorem le_normalizer_opResidual (P : Subgroup (MulAut V)) :
    P ≤ Subgroup.normalizer ((opResidual 2 P : Subgroup (MulAut V)) : Set (MulAut V)) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (opResidual_le 2 P)).1 (opResidual_normal 2 P)

omit [Finite V] in
theorem le_stabSub_fixOp (P : Subgroup (MulAut V)) : P ≤ stabSub (fixOp P) := fun _ hg v =>
  mem_fixV_normalizer_iff (le_normalizer_opResidual P hg) v

@[expose] noncomputable def quotHom (P : Subgroup (MulAut V)) : ↥P →* MulAut (V ⧸ fixOp P) :=
  (quotAct (fixOp P)).comp (Subgroup.inclusion (le_stabSub_fixOp P))

omit [Finite V] in
theorem quotHom_mk (P : Subgroup (MulAut V)) (g : ↥P) (v : V) :
    quotHom P g (QuotientGroup.mk v) = QuotientGroup.mk ((g : MulAut V) v) := rfl

omit [Finite V] in
theorem mem_ker_quotHom (P : Subgroup (MulAut V)) (g : ↥P) :
    g ∈ (quotHom P).ker ↔ ∀ v : V, (g : MulAut V) v * v⁻¹ ∈ fixOp P := by
  have := mem_ker_quotAct (fixOp P) (Subgroup.inclusion (le_stabSub_fixOp P) g)
  rw [MonoidHom.mem_ker] at this ⊢
  exact this

omit [Finite V] in
theorem opResidual_le_closure_odd (P : Subgroup (MulAut V)) :
    opResidual 2 P ≤ Subgroup.closure {x | x ∈ opResidual 2 P ∧ Odd (orderOf x)} := by
  refine (Subgroup.closure_le _).2 fun x hx => Subgroup.subset_closure ⟨?_, ?_⟩
  · exact mem_opResidual_of_coprime hx.1 hx.2
  · exact Nat.coprime_two_right.1 hx.2

theorem false_of_opResidual_le_bot' {P T M : Subgroup (MulAut V)} (hmin : MinPar P T M)
    (hres : opResidual 2 P ≤ ⊥) : False := by
  have hP2 : IsPGroup 2 ↥P := by
    intro x
    obtain ⟨k, hk⟩ := exists_pow_mem_opResidual (p := 2) (A := P) x.2
    refine ⟨k, Subtype.ext ?_⟩
    have := hres hk
    simpa using this
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP2
  have hrel := Subgroup.relIndex_mul_card (H := T) (K := P)
  rw [inf_eq_left.2 hmin.T_le, hn] at hrel
  have hdvd : T.relIndex P ∣ 2 ^ n := ⟨Nat.card T, hrel.symm⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    by_contra hne
    exact hmin.syl.2.2 (hi ▸ dvd_pow_self 2 hne)
  rw [hi0, pow_zero] at hi
  have hPT : P ≤ T := Subgroup.relIndex_eq_one.1 hi
  exact hmin.not_normal (hPT.trans Subgroup.le_normalizer)

theorem quotHom_injective (hV : ∀ v : V, v ^ 2 = 1) {P T M : Subgroup (MulAut V)}
    (hmin : MinPar P T M) (ho2 : pCoreOf 2 P = ⊥) : Function.Injective (quotHom P) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  set C : Subgroup (MulAut V) := (quotHom P).ker.map P.subtype with hC
  have hCP : C ≤ P := Subgroup.map_subtype_le _
  have hCsub : C.subgroupOf P = (quotHom P).ker :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hCn : P ≤ Subgroup.normalizer (C : Set (MulAut V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCP).1 (hCsub ▸ MonoidHom.normal_ker _)
  have hkey : ∀ c ∈ C, ∀ v : V, c v * v⁻¹ ∈ fixOp P := by
    rintro _ ⟨c', hc', rfl⟩ v
    exact (mem_ker_quotHom P c').1 hc' v
  have hbot : ∀ K : Subgroup (MulAut V), K ≤ opResidual 2 P →
      K ≤ Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)} →
      (∀ k ∈ K, ∀ v : V, k v * v⁻¹ ∈ fixOp P) → K = ⊥ := by
    intro K hKO hKgen hK
    refine (Subgroup.eq_bot_iff_forall K).2 fun k hk => MulEquiv.ext fun v => ?_
    exact fix_of_quad_oddGen hV hKgen (fun k hk k' hk' => hK k hk v k' (hKO hk')) k hk
  by_cases hCM : C ≤ M
  ·
    have h33 := three_three_a hmin.syl hmin.lt_P hmin.max hCP hCn hCM
    have hCT : C ⊓ T ≤ ⊥ := ho2 ▸ le_pCoreOf_of_le_normalizer 2
      (inf_le_right.trans hmin.T_le) h33 (hmin.syl.2.1.to_le inf_le_right)
    have hSyl := FourTwoTools.isSylowOf_inf_of_le_normalizer hmin.syl hCP hCn
    have hodd : ¬ 2 ∣ Nat.card C := by
      have h1 := hSyl.2.2
      rw [le_bot_iff.1 hCT, Subgroup.relIndex_bot_left] at h1
      exact h1
    have hoddOrd : ∀ c ∈ C, Odd (orderOf c) := by
      intro c hc
      have h1 : orderOf c ∣ Nat.card C := by
        show orderOf ((⟨c, hc⟩ : C) : MulAut V) ∣ Nat.card C
        rw [Subgroup.orderOf_coe]
        exact orderOf_dvd_natCard _
      by_contra hev
      exact hodd ((even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)).trans h1)
    have hCO : C ≤ opResidual 2 P := fun c hc =>
      mem_opResidual_of_coprime (hCP hc) (Nat.coprime_two_right.2 (hoddOrd c hc))
    have hCbot := hbot C hCO (fun c hc => Subgroup.subset_closure ⟨hc, hoddOrd c hc⟩) hkey
    have : (g : MulAut V) ∈ C := ⟨g, hg, rfl⟩
    rw [hCbot, Subgroup.mem_bot] at this
    exact Subtype.ext this
  ·
    have hOC := three_three_b hmin.syl hmin.max hCP hCn hCM
    have hObot : opResidual 2 P = ⊥ :=
      hbot _ le_rfl (opResidual_le_closure_odd P) fun x hx => hkey x (hOC hx)
    exact (false_of_opResidual_le_bot' hmin (le_of_eq hObot)).elim

section Offender

variable {P : Subgroup (MulAut V)}

omit [Finite V] in
theorem mk_mem_fixV_map {B : Subgroup (MulAut V)} {v : V} (hv : v ∈ fixV B) :
    (QuotientGroup.mk v : V ⧸ fixOp P) ∈ fixV ((B.subgroupOf P).map (quotHom P)) := by
  rintro _ ⟨b, hb, rfl⟩
  rw [quotHom_mk]
  exact congrArg QuotientGroup.mk (hv b (Subgroup.mem_subgroupOf.1 hb))

theorem card_fixV_le_quot {B : Subgroup (MulAut V)} :
    Nat.card (fixV B) ≤
      Nat.card (fixV ((B.subgroupOf P).map (quotHom P))) * Nat.card (fixOp P) := by
  let φ : ↥(fixV B) →* ↥(fixV ((B.subgroupOf P).map (quotHom P))) :=
    MonoidHom.codRestrict ((QuotientGroup.mk' (fixOp P)).comp (fixV B).subtype)
      (fixV ((B.subgroupOf P).map (quotHom P))) fun v => mk_mem_fixV_map v.2
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.ker ≤ Nat.card (fixOp P) := by
    refine Nat.card_le_card_of_injective (fun x => (⟨(x : ↥(fixV B)), ?_⟩ : ↥(fixOp P))) ?_
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have := congrArg (fun y : ↥(fixV ((B.subgroupOf P).map (quotHom P))) =>
        (y : V ⧸ fixOp P)) hx
      exact (QuotientGroup.eq_one_iff _).1 this
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥(fixOp P) => (z : V)) hxy))
  have h3 : Nat.card φ.range ≤ Nat.card (fixV ((B.subgroupOf P).map (quotHom P))) :=
    Subgroup.card_le_card_group _
  rw [← h1]
  exact Nat.mul_le_mul h3 h2 |>.trans_eq' (by ring) |>.trans (le_of_eq (by ring))

omit [Finite V] in
theorem isElemAbelian2_map_quot {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) :
    IsElemAbelian2 ((A.subgroupOf P).map (quotHom P)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 x (Subgroup.mem_subgroupOf.1 hx) y (Subgroup.mem_subgroupOf.1 hy))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (hA.2 x (Subgroup.mem_subgroupOf.1 hx))
    rw [this, map_one]

theorem exists_isOff_quot (hinj : Function.Injective (quotHom P))
    (hoff : ∃ A : Subgroup (MulAut V), A ≤ P ∧ IsOff A) :
    ∃ B : Subgroup (MulAut (V ⧸ fixOp P)), B ≤ (⊤ : Subgroup ↥P).map (quotHom P) ∧ IsOff B := by
  obtain ⟨A, hAP, hAoff⟩ := hoff
  set Ã : Subgroup (MulAut (V ⧸ fixOp P)) := (A.subgroupOf P).map (quotHom P) with hÃ
  have hcardÃ : Nat.card Ã = Nat.card A := by
    rw [hÃ, Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
  have hZpos : 0 < Nat.card (fixOp P) := Nat.card_pos
  have hVcard : Nat.card V = Nat.card (V ⧸ fixOp P) * Nat.card (fixOp P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (fixOp P)
  have hwÃ : Nat.card (V ⧸ fixOp P) ≤ Nat.card Ã * Nat.card (fixV Ã) := by
    have h1 : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := hAoff.card_le_wt
    have h2 := card_fixV_le_quot (P := P) (B := A)
    refine Nat.le_of_mul_le_mul_right ?_ hZpos
    calc Nat.card (V ⧸ fixOp P) * Nat.card (fixOp P) = Nat.card V := hVcard.symm
      _ ≤ Nat.card A * Nat.card (fixV A) := h1
      _ ≤ Nat.card A * (Nat.card (fixV Ã) * Nat.card (fixOp P)) := Nat.mul_le_mul_left _ h2
      _ = Nat.card Ã * Nat.card (fixV Ã) * Nat.card (fixOp P) := by rw [hcardÃ]; ring
  obtain ⟨B₀, hB₀, hmax⟩ := Set.exists_max_image
    {B : Subgroup (MulAut (V ⧸ fixOp P)) | B ≤ Ã}
    (fun B => Nat.card B * Nat.card (fixV B)) (Set.toFinite _) ⟨⊥, (bot_le : ⊥ ≤ Ã)⟩
  obtain ⟨B₁, ⟨hB₁, hB₁w⟩, hmax2⟩ := Set.exists_max_image
    {B : Subgroup (MulAut (V ⧸ fixOp P)) |
      B ≤ Ã ∧ Nat.card B * Nat.card (fixV B) = Nat.card B₀ * Nat.card (fixV B₀)}
    (fun B => Nat.card B) (Set.toFinite _) ⟨B₀, hB₀, rfl⟩
  have hB₁ne : B₁ ≠ ⊥ := by
    intro hbot
    have hw1 : Nat.card B₁ * Nat.card (fixV B₁) = Nat.card (V ⧸ fixOp P) := by
      rw [hbot]
      exact B1.card_bot_mul_card_fixV
    have hÃle : Nat.card Ã * Nat.card (fixV Ã) ≤ Nat.card B₀ * Nat.card (fixV B₀) :=
      hmax Ã (le_rfl : Ã ≤ Ã)
    have hÃeq : Nat.card Ã * Nat.card (fixV Ã) = Nat.card B₀ * Nat.card (fixV B₀) := by
      refine le_antisymm hÃle ?_
      rw [← hB₁w, hw1]
      exact hwÃ
    have h3 := hmax2 Ã ⟨(le_rfl : Ã ≤ Ã), hÃeq⟩
    have h4 : Nat.card B₁ = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h5 : Nat.card A = 1 := by
      have h6 : Nat.card Ã ≤ 1 := (show Nat.card Ã ≤ Nat.card B₁ from h3).trans h4.le
      have h7 : 0 < Nat.card Ã := Nat.card_pos
      rw [← hcardÃ]
      omega
    exact hAoff.2.1 (Subgroup.card_eq_one.1 h5)
  refine ⟨B₁, hB₁.trans (Subgroup.map_mono le_top), le_top, hB₁ne,
    isElemAbelian2_mono' (isElemAbelian2_map_quot hAoff.2.2.1) hB₁, fun C hC => ?_⟩
  have := hmax C (hC.trans hB₁)
  rw [← hB₁w] at this
  exact this

end Offender

section Hyp

variable {P T M : Subgroup (MulAut V)}

omit [Finite V] in
theorem quot_sq_eq_one (hV : ∀ v : V, v ^ 2 = 1) (Z : Subgroup V) (x : V ⧸ Z) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H v => rw [← QuotientGroup.mk_pow, hV v, QuotientGroup.mk_one]

theorem not_forall_fix_quot (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M)
    (hinj : Function.Injective (quotHom P)) :
    ¬ ∀ g ∈ (⊤ : Subgroup ↥P).map (quotHom P),
      ∀ u ∈ fixV ((T.subgroupOf P).map (quotHom P)), g u = u := by
  intro hcen
  have hker : (quotHom P).ker ⊓ (⊤ : Subgroup ↥P) ≤ M.subgroupOf P := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
    exact inf_le_left.trans bot_le
  have hmin' := MinPar.map_of_ker_le (quotHom P) hmin.subgroupOf_top hker
  have hnt : (⊤ : Subgroup (V ⧸ fixOp P)) ≠ ⊥ := by
    intro htop
    apply hmin.not_normal
    intro g hg
    have h1 : ∀ x : V ⧸ fixOp P, x = 1 := fun x =>
      (Subgroup.mem_bot.1 (htop ▸ Subgroup.mem_top x))
    have : (⟨g, hg⟩ : ↥P) = 1 := hinj (MulEquiv.ext fun x => (h1 _).trans (h1 _).symm)
    have hg1 : g = 1 := congrArg Subtype.val this
    rw [hg1]
    exact Subgroup.one_mem _
  obtain ⟨m, -, hm1, hmfix⟩ := B1.exists_fixed_ne_one (quot_sq_eq_one hV (fixOp P))
    hmin'.syl.2.1 (fun _ _ _ _ => Subgroup.mem_top _) hnt
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective m
  have hfixP : ∀ g : ↥P, ((g : MulAut V) v) * v⁻¹ ∈ fixOp P := by
    intro g
    have h1 := hcen (quotHom P g) (Subgroup.mem_map_of_mem _ (Subgroup.mem_top g))
      (QuotientGroup.mk v) hmfix
    rw [quotHom_mk] at h1
    have h2 := QuotientGroup.eq.1 h1
    have h3 := (fixOp P).inv_mem h2
    rwa [mul_inv_rev, inv_inv, mul_comm] at h3
  have hvfix : v ∈ fixOp P := by
    intro x hx
    exact fix_of_quad_oddGen hV (opResidual_le_closure_odd P)
      (fun k hk k' hk' => hfixP ⟨k, opResidual_le 2 P hk⟩ k' hk') x hx
  exact hm1 ((QuotientGroup.eq_one_iff v).2 hvfix)

theorem hyp51_quot (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M) (ho2 : pCoreOf 2 P = ⊥)
    (hoff : ∃ A : Subgroup (MulAut V), A ≤ P ∧ IsOff A) :
    Hyp51 ((⊤ : Subgroup ↥P).map (quotHom P)) ((T.subgroupOf P).map (quotHom P))
      ((M.subgroupOf P).map (quotHom P)) := by
  have hinj := quotHom_injective hV hmin ho2
  have hker : (quotHom P).ker ⊓ (⊤ : Subgroup ↥P) ≤ M.subgroupOf P := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
    exact inf_le_left.trans bot_le
  have hmin' := MinPar.map_of_ker_le (quotHom P) hmin.subgroupOf_top hker
  have hO2 : pCoreOf 2 (⊤ : Subgroup ↥P) ≤ (quotHom P).ker := by
    intro q hq
    have hn : (pCoreOf 2 (⊤ : Subgroup ↥P)).Normal :=
      ⟨fun x hx g => (Subgroup.mem_normalizer_iff.1
        (le_normalizer_pCoreOf 2 (⊤ : Subgroup ↥P) (Subgroup.mem_top g)) x).1 hx⟩
    have hN : (pCoreOf 2 (⊤ : Subgroup ↥P)).map P.subtype ≤ pCoreOf 2 P := by
      refine le_pCoreOf 2 (Subgroup.map_subtype_le _) ?_ ((pCoreOf_isPGroup 2 _).map _)
      have h1 : ((pCoreOf 2 (⊤ : Subgroup ↥P)).map P.subtype).subgroupOf P =
          pCoreOf 2 (⊤ : Subgroup ↥P) :=
        Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
      rw [h1]
      exact hn
    have h2 : (q : MulAut V) ∈ pCoreOf 2 P := hN ⟨q, hq, rfl⟩
    rw [ho2, Subgroup.mem_bot] at h2
    have hq1 : q = 1 := Subtype.ext h2
    rw [hq1]
    exact (quotHom P).ker.one_mem
  refine ⟨hmin', pCoreOf_map_eq_bot_of_ker_le (quotHom P) hmin.subgroupOf_top hker hO2,
    exists_isOff_quot hinj hoff, ?_⟩
  intro y hy
  by_contra hyM
  have hYle : cenIn ((⊤ : Subgroup ↥P).map (quotHom P))
      (fixV ((T.subgroupOf P).map (quotHom P))) ≤ (⊤ : Subgroup ↥P).map (quotHom P) :=
    cenIn_le _ _
  have hTY : (T.subgroupOf P).map (quotHom P) ≤ cenIn ((⊤ : Subgroup ↥P).map (quotHom P))
      (fixV ((T.subgroupOf P).map (quotHom P))) := fun t ht =>
    ⟨Subgroup.map_mono le_top ht, fun u hu => hu t ht⟩
  have hlt : cenIn ((⊤ : Subgroup ↥P).map (quotHom P))
      (fixV ((T.subgroupOf P).map (quotHom P))) < (⊤ : Subgroup ↥P).map (quotHom P) := by
    refine lt_of_le_of_ne hYle fun heq => not_forall_fix_quot hV hmin hinj fun g hg u hu => ?_
    have : g ∈ cenIn ((⊤ : Subgroup ↥P).map (quotHom P))
        (fixV ((T.subgroupOf P).map (quotHom P))) := by
      rw [heq]
      exact hg
    exact this.2 u hu
  exact hyM (hmin'.max _ hTY hlt hy)

end Hyp

end CFSG.CGT.PushingUpLit.BHS5
