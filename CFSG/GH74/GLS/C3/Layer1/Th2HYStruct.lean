module

public import CFSG.GH74.GLS.C3.Layer1.Th2HYPump
public import CFSG.GH74.GLS.C3.Layer1.Th2P812Frat

public section

namespace CFSG.GH74.GLS.Th2.HY

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev lamV (K V : Subgroup G) : Subgroup G :=
  twoGen (K ⊓ centralizer (V : Set G))

abbrev OV (V : Subgroup G) : Subgroup G := pPrimeCoreOf 2 (normalizer (V : Set G))

abbrev HV (K V : Subgroup G) : Subgroup G := lamV K V ⊔ OV V

abbrev YV (K V : Subgroup G) : Subgroup G :=
  normalizer (V : Set G) ⊓ centralizerSection (HV K V) (OV V)

structure HYSetup (x y : G) (K T S V : Subgroup G) : Prop where
  std : Th2Std x y K T S
  simple : IsSimpleGroup (kBar K)
  cen : CenterlessBar K
  hVQ : V ≤ T ⊓ CxK x K
  hVel : CFSG.IsElementaryAbelian 2 ↥V
  hVne : V ≠ ⊥

theorem isSylowOf_of_le_of_le [Finite G] {P A B : Subgroup G} (hP : IsSylowOf 2 P B) (hPA : P ≤ A)
    (hAB : A ≤ B) : IsSylowOf 2 P A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨-, hp, hdvd⟩ := hP
  refine ⟨hPA, hp, fun h2 => hdvd ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P A B hPA hAB]
  exact h2.mul_right _

theorem mem_CMbar_of_comm [Finite G] {M K : Subgroup G} (hKM : K ≤ M) {y : G} (hyM : y ∈ M)
    (hc : ∀ k ∈ K, ⁅k, y⁆ ∈ pPrimeCoreOf 2 M) : y ∈ CMbar M K := by
  set O : Subgroup G := pPrimeCoreOf 2 M with hO
  have hNO : y ∈ normalizer (O : Set G) :=
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hyM)
  have hKN : K ≤ normalizer (O : Set G) := fun k hk =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hKM hk))
  have hOn : ∀ g ∈ M, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    TwoThin.pPrimeCoreOf_normalized M hg ho
  have hcomm : ∀ a ∈ K ⊔ O, ⁅a, y⁆ ∈ O := by
    intro a ha
    obtain ⟨k, hk, o, ho, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hKN).1 ha
    have e : ⁅k * o, y⁆ = k * ⁅o, y⁆ * k⁻¹ * ⁅k, y⁆ := by
      simp only [commutatorElement_def]; group
    have h1 : ⁅o, y⁆ ∈ O := by
      have : ⁅o, y⁆ = o * (y * o⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact O.mul_mem ho (hOn y hyM _ (O.inv_mem ho))
    rw [e]
    exact O.mul_mem (hOn k (hKM hk) _ h1) (hc k hk)
  have hOA : O ≤ K ⊔ O := le_sup_right
  have h1 : ∀ b ∈ K ⊔ O, y * b * y⁻¹ ∈ K ⊔ O := by
    intro b hb
    have : y * b * y⁻¹ = (⁅b, y⁆)⁻¹ * b := by simp only [commutatorElement_def]; group
    rw [this]
    exact (K ⊔ O).mul_mem (hOA (O.inv_mem (hcomm b hb))) hb
  have h2 : ∀ b ∈ K ⊔ O, y⁻¹ * b * y ∈ K ⊔ O := by
    intro b hb
    have : y⁻¹ * b * y = (y⁻¹ * ⁅b, y⁆ * y) * b := by simp only [commutatorElement_def]; group
    rw [this]
    exact (K ⊔ O).mul_mem (hOA (by simpa using hOn y⁻¹ ((M).inv_mem hyM) _ (hcomm b hb))) hb
  refine ⟨hyM, ?_, hNO, hcomm⟩
  rw [Subgroup.mem_normalizer_iff]
  intro a
  exact ⟨fun ha => h1 a ha, fun ha => by simpa [mul_assoc] using h2 _ ha⟩

theorem exists_centralizing_mem_coset_of_primeAction [Finite G] {K V : Subgroup G}
    (hVK : V ≤ normalizer (K : Set G))
    (hVO : V ≤ normalizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G))
    (hV2 : IsPGroup 2 ↥V)
    (hVcomm : ∀ v ∈ V, ∀ k ∈ K, ⁅k, v⁆ ∈ pPrimeCoreOf 2 K)
    {k : G} (hk : k ∈ K) :
    ∃ c ∈ K ⊓ centralizer (V : Set G), k⁻¹ * c ∈ pPrimeCoreOf 2 K := by
  obtain ⟨c, hcK, hcV, hcO⟩ := exists_fixed_mem_coset_gen (K := K) (Q := V)
    (N' := pPrimeCoreOf 2 K) hV2
    (fun q hq k hk => (Subgroup.mem_normalizer_iff.1 (hVK hq) k).1 hk)
    (fun q hq o ho => (Subgroup.mem_normalizer_iff.1 (hVO hq) o).1 ho)
    (fun k hk o ho => TwoThin.pPrimeCoreOf_normalized K hk ho)
    (TwoThin.pPrimeCoreOf_le K) (TwoThin.card_pPrimeCoreOf_odd K) hk
    (fun q hq => hVcomm q hq k hk)
  exact ⟨c, ⟨hcK, Subgroup.mem_centralizer_iff.2 (fun w hw => (hcV w hw).symm)⟩, hcO⟩

theorem lam_cover_of_primeResidual_eq_top [Finite G] {K V : Subgroup G}
    (hgen : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 2 ↥K = ⊤)
    (hVK : V ≤ normalizer (K : Set G))
    (hVO : V ≤ normalizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G))
    (hV2 : IsPGroup 2 ↥V)
    (hVcomm : ∀ v ∈ V, ∀ k ∈ K, ⁅k, v⁆ ∈ pPrimeCoreOf 2 K) :
    ∀ k ∈ K, ∃ l ∈ lamV K V, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup G := pPrimeCoreOf 2 K
  let C : Subgroup G := K ⊓ centralizer (V : Set G)
  have hOodd : Odd (Nat.card ↥O) := TwoThin.card_pPrimeCoreOf_odd K
  have hCO : C ≤ normalizer (O : Set G) := fun c hc =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hc.1)
  have hΛK : lamV K V ≤ K := (twoGen_le _).trans inf_le_left
  have hΛO : lamV K V ≤ normalizer (O : Set G) := fun l hl =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hΛK hl))
  have hgenK : K ≤ Subgroup.closure {g : G | g ∈ K ∧ ∃ n : ℕ, orderOf g = 2 ^ n} := by
    have h := congrArg (Subgroup.map K.subtype) hgen
    rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure,
      MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype] at h
    calc K = Subgroup.closure (K.subtype '' {y : ↥K | ∃ n : ℕ, orderOf y = 2 ^ n}) := h.symm
      _ ≤ Subgroup.closure {g : G | g ∈ K ∧ ∃ n : ℕ, orderOf g = 2 ^ n} := by
          refine Subgroup.closure_mono ?_
          rintro g ⟨y, ⟨n, hn⟩, rfl⟩
          exact ⟨y.2, n, (Subgroup.orderOf_coe y).trans hn⟩
  have hKle : K ≤ lamV K V ⊔ O := by
    refine hgenK.trans ((Subgroup.closure_le (lamV K V ⊔ O)).2 ?_)
    rintro t ⟨htK, n, htn⟩
    obtain ⟨c, hcC, hco⟩ :=
      exists_centralizing_mem_coset_of_primeAction hVK hVO hV2 hVcomm htK
    obtain ⟨o, ho, hco'⟩ : ∃ o ∈ O, c = t * o := ⟨t⁻¹ * c, hco, by group⟩
    have ht : t = c * o⁻¹ := by rw [hco']; group
    have htCO : t ∈ C ⊔ O := by
      rw [mem_sup_iff_mul_of_le_normalizer hCO]
      exact ⟨c, hcC, o⁻¹, O.inv_mem ho, ht⟩
    have htpow : t ^ (2 ^ n) = 1 := by rw [← htn]; exact pow_orderOf_eq_one t
    have hmem : t ∈ twoGen C ⊔ O := twoElt_mem_sup hCO hOodd htCO htpow
    simpa [C, O, lamV] using hmem
  intro k hk
  obtain ⟨l, hl, o, ho, hko⟩ := (mem_sup_iff_mul_of_le_normalizer hΛO).1 (hKle hk)
  exact ⟨l, hl, o, ho, hko⟩

theorem lam_cover_of_isPCompIn [Finite G] {x : G} {K V : Subgroup G}
    (hK : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) K)
    (hVQ : V ≤ CxK x K) (hV2 : IsPGroup 2 ↥V) :
    ∀ k ∈ K, ∃ l ∈ lamV K V, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 2 ↥K = ⊤ :=
    ((CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K
      (Subgroup.centralizer ({x} : Set G)) hK.1).mp hK.2).2.1
  exact lam_cover_of_primeResidual_eq_top hgen
    (fun v hv => (hVQ hv).2.1)
    (fun v hv => (hVQ hv).2.2.1)
    hV2
    (fun v hv k hk => (hVQ hv).2.2.2 k hk)

namespace HYSetup

variable {x y : G} {K T S V : Subgroup G}

theorem hKq [Finite G] (hS : HYSetup x y K T S V) : CFSG.IsQuasisimple (kBar K) :=
  TwoThin.isQuasisimple_hat hS.std.comp

theorem V_pGroup [Finite G] (hS : HYSetup x y K T S V) : IsPGroup 2 ↥V :=
  hS.std.T_pGroup.to_le (hS.hVQ.trans inf_le_left)

theorem P_le_X [Finite G] (hS : HYSetup x y K T S V) : T ⊓ K ≤ K ⊓ centralizer (V : Set G) := by
  intro p hp
  refine ⟨hp.2, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
  exact ((hS.std.commDisj hS.cen).comm p hp w (hS.hVQ hw)).symm

theorem P_le_lamV [Finite G] (hS : HYSetup x y K T S V) : T ⊓ K ≤ lamV K V :=
  le_twoGen_of_isPGroup (hS.std.T_pGroup.to_le inf_le_left) hS.P_le_X

theorem kBar_even [Finite G] (hS : HYSetup x y K T S V) : 2 ∣ Nat.card (kBar K) := by
  obtain ⟨W, -, hW4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hS.hKq
      (by rw [Th2.PumpTerm.center_eq_bot_of_centerlessBar hS.cen, Subgroup.card_bot]; exact odd_one))
  have := Subgroup.card_subgroup_dvd_card W
  rw [hW4] at this
  exact (by norm_num : 2 ∣ 4).trans this

theorem lamV_le_N (K V : Subgroup G) : lamV K V ≤ normalizer (V : Set G) :=
  (twoGen_le _).trans (inf_le_right.trans (fun _ ha => Subgroup.centralizer_le_normalizer (V : Set G) ha))

theorem lamV_le_normalizer_OV [Finite G] (K V : Subgroup G) :
    lamV K V ≤ normalizer ((OV V : Subgroup G) : Set G) := fun _ ha =>
  TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (lamV_le_N K V ha))

theorem HV_le_N [Finite G] (K V : Subgroup G) : HV K V ≤ normalizer (V : Set G) :=
  sup_le (lamV_le_N K V) (TwoThin.pPrimeCoreOf_le _)

theorem hnormH [Finite G] (hG : C3Hyp G) (hS : HYSetup x y K T S V) :
    ∀ n ∈ normalizer (V : Set G), ∀ h ∈ HV K V, n * h * n⁻¹ ∈ HV K V := by
  intro n hn h hh
  obtain ⟨l, hl, o, ho, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer (lamV_le_normalizer_OV K V)).1 hh
  have h1 : n * l * n⁻¹ ∈ HV K V := by
    have := lam_conj_le hG hS.std hS.hKq hS.cen hS.hVQ hS.hVel hS.hVne hn
    exact this ⟨l, hl, by simp [MulAut.conj_apply]⟩
  have h2 : n * o * n⁻¹ ∈ OV V :=
    (Subgroup.mem_normalizer_iff.1
      (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hn)) o).1 ho
  have : n * (l * o) * n⁻¹ = (n * l * n⁻¹) * (n * o * n⁻¹) := by group
  rw [this]
  exact (HV K V).mul_mem h1 (Subgroup.mem_sup_right h2)

theorem lam_cover [Finite G] (hS : HYSetup x y K T S V) :
    ∀ k ∈ K, ∃ l ∈ lamV K V, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o :=
  lam_cover_of_isPCompIn hS.std.comp (hS.hVQ.trans inf_le_right) hS.V_pGroup

theorem lam_inf_O_le [Finite G] (hS : HYSetup x y K T S V) :
    lamV K V ⊓ OV V ≤ pPrimeCoreOf 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥K →* kBar K := QuotientGroup.mk' (pPrimeCore 2 ↥K)
  let B : Subgroup G := lamV K V ⊓ OV V
  have hLK : lamV K V ≤ K := (twoGen_le _).trans inf_le_left
  have hBK : B ≤ K := inf_le_left.trans hLK
  let C : Subgroup (kBar K) := (B.subgroupOf K).map π
  have hCnorm : C.Normal := by
    refine ⟨fun a ha b => ?_⟩
    obtain ⟨β, hβ, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨l, hl, o, ho, hk⟩ := hS.lam_cover k k.2
    have hlK : l ∈ K := hLK hl
    have hoK : o ∈ K := TwoThin.pPrimeCoreOf_le K ho
    have hb : (QuotientGroup.mk k : kBar K) = π ⟨l, hlK⟩ := by
      obtain ⟨hoK', ho'⟩ := C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.1 ho
      have : k⁻¹ * ⟨l, hlK⟩ = (⟨o, hoK⟩ : ↥K)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hk]
        group
      show (QuotientGroup.mk k : kBar K) = QuotientGroup.mk ⟨l, hlK⟩
      rw [QuotientGroup.eq, this]
      exact (pPrimeCore 2 ↥K).inv_mem ho'
    refine ⟨⟨l, hlK⟩ * β * ⟨l, hlK⟩⁻¹, ?_, ?_⟩
    · show (⟨l, hlK⟩ * β * ⟨l, hlK⟩⁻¹ : ↥K) ∈ B.subgroupOf K
      rw [Subgroup.mem_subgroupOf]
      have hβ' := Subgroup.mem_subgroupOf.1 hβ
      refine ⟨?_, ?_⟩
      · simpa using (lamV K V).mul_mem ((lamV K V).mul_mem hl hβ'.1) ((lamV K V).inv_mem hl)
      · simpa using (Subgroup.mem_normalizer_iff.1 (lamV_le_normalizer_OV K V hl) (β : G)).1 hβ'.2
    · rw [hb]
      simp [π]
  have hCn := hCnorm
  rcases hS.simple.eq_bot_or_eq_top_of_normal C with hbot | htop
  · intro b hb
    have hbC : π ⟨b, hBK hb⟩ ∈ C := ⟨⟨b, hBK hb⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hbC
    exact C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hBK hb, (QuotientGroup.eq_one_iff _).1 hbC⟩
  · exfalso
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hS.kBar_even
    have htC : t ∈ C := htop ▸ Subgroup.mem_top _
    obtain ⟨β, hβ, rfl⟩ := htC
    have hβB : (β : G) ∈ B := Subgroup.mem_subgroupOf.1 hβ
    have h1 : orderOf (π β) ∣ orderOf β := orderOf_map_dvd π β
    have h2 : orderOf β ∣ Nat.card (OV V) := by
      rw [← Subgroup.orderOf_coe β]
      exact Subgroup.orderOf_dvd_natCard _ hβB.2
    rw [ht] at h1
    have h3 : 2 ∣ Nat.card (OV V) := h1.trans h2
    exact (Nat.not_even_iff_odd.2 (TwoThin.card_pPrimeCoreOf_odd _)) (even_iff_two_dvd.2 h3)

theorem mem_normalizer_HV [Finite G] (hG : C3Hyp G) (hS : HYSetup x y K T S V) {n : G}
    (hn : n ∈ normalizer (V : Set G)) : n ∈ normalizer ((HV K V : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hS.hnormH hG n hn h hh, fun hh => ?_⟩
  have := hS.hnormH hG n⁻¹ (inv_mem hn) _ hh
  simpa [mul_assoc] using this

theorem mem_OK_of_comm [Finite G] (hS : HYSetup x y K T S V) {l : G} (hl : l ∈ lamV K V)
    (hc : ∀ l' ∈ lamV K V, ⁅l', l⁆ ∈ pPrimeCoreOf 2 K) : l ∈ pPrimeCoreOf 2 K := by
  have hLK : lamV K V ≤ K := (twoGen_le _).trans inf_le_left
  refine mem_pPrimeCoreOf_of_commutators hS.cen (hLK hl) (fun k hk => ?_)
  obtain ⟨l', hl', o, ho, rfl⟩ := hS.lam_cover k hk
  have e : ⁅l' * o, l⁆ = l' * ⁅o, l⁆ * l'⁻¹ * ⁅l', l⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have h1 : ⁅o, l⁆ ∈ pPrimeCoreOf 2 K := by
    have : ⁅o, l⁆ = o * (l * o⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact (pPrimeCoreOf 2 K).mul_mem ho
      (TwoThin.pPrimeCoreOf_normalized K (hLK hl) ((pPrimeCoreOf 2 K).inv_mem ho))
  exact (pPrimeCoreOf 2 K).mul_mem (TwoThin.pPrimeCoreOf_normalized K (hLK hl') h1) (hc l' hl')

theorem lam_inf_OK_le_OV [Finite G] (hG : C3Hyp G) (hS : HYSetup x y K T S V) :
    lamV K V ⊓ pPrimeCoreOf 2 K ≤ OV V := by
  have hLK : lamV K V ≤ K := (twoGen_le _).trans inf_le_left
  have hLN := lamV_le_normalizer_OV K V
  have hZN : lamV K V ⊓ pPrimeCoreOf 2 K ≤ normalizer ((OV V : Subgroup G) : Set G) :=
    inf_le_left.trans hLN
  set Z : Subgroup G := lamV K V ⊓ pPrimeCoreOf 2 K with hZ
  set R : Subgroup G := Z ⊔ OV V with hR
  have hRodd : Odd (Nat.card R) := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hZN
    have hZodd : Odd (Nat.card Z) := (TwoThin.card_pPrimeCoreOf_odd K).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_right)
    have : Odd (Nat.card Z * Nat.card (OV V)) := hZodd.mul (TwoThin.card_pPrimeCoreOf_odd _)
    rw [← h1] at this
    exact (Nat.odd_mul.1 this).1
  have hRH : R ≤ HV K V := sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hl : ∀ l ∈ lamV K V, ∀ r ∈ R, l * r * l⁻¹ ∈ R := by
    intro l hl r hr
    obtain ⟨z, hz, o, ho, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hZN).1 hr
    have h1 : l * z * l⁻¹ ∈ Z := ⟨(lamV K V).mul_mem ((lamV K V).mul_mem hl hz.1)
      ((lamV K V).inv_mem hl), TwoThin.pPrimeCoreOf_normalized K (hLK hl) hz.2⟩
    have h2 : l * o * l⁻¹ ∈ OV V := (Subgroup.mem_normalizer_iff.1 (hLN hl) o).1 ho
    have : l * (z * o) * l⁻¹ = (l * z * l⁻¹) * (l * o * l⁻¹) := by group
    rw [this]
    exact R.mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  have hRnorm : ∀ h ∈ HV K V, ∀ r ∈ R, h * r * h⁻¹ ∈ R := by
    intro h hh r hr
    obtain ⟨l, hl', o, ho', rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hLN).1 hh
    have hor : o * r * o⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (Subgroup.mem_sup_right ho') hr) (R.inv_mem (Subgroup.mem_sup_right ho'))
    have : l * o * r * (l * o)⁻¹ = l * (o * r * o⁻¹) * l⁻¹ := by group
    rw [this]
    exact hl l hl' _ hor
  have h1 : R ≤ pPrimeCoreOf 2 (HV K V) := le_pPrimeCoreOf_of_norm hRH hRnorm hRodd
  have h2 : pPrimeCoreOf 2 (HV K V) ≤ OV V :=
    le_pPrimeCoreOf_of_norm ((TwoThin.pPrimeCoreOf_le _).trans (HV_le_N K V))
      (fun n hn o ho => (Subgroup.mem_normalizer_iff.1
        (TwoThin.mem_normalizer_pPrimeCoreOf (hS.mem_normalizer_HV hG hn)) o).1 ho)
      (TwoThin.card_pPrimeCoreOf_odd _)
  exact (le_sup_left.trans h1).trans h2

theorem map_conj_of_mem_normalizer {A : Subgroup G} {q : G} (hq : q ∈ normalizer (A : Set G)) :
    A.map (MulAut.conj q).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hq a).1 ha
    simpa [MulAut.conj_apply] using this
  · intro hx
    refine ⟨q⁻¹ * x * q, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hq) x).1 hx
    simpa using this

theorem conj_mem_lamV [Finite G] {q : G} (hqK : q ∈ normalizer (K : Set G))
    (hqV : q ∈ normalizer (V : Set G)) {l : G} (hl : l ∈ lamV K V) : q * l * q⁻¹ ∈ lamV K V := by
  have hX : (K ⊓ centralizer (V : Set G)).map (MulAut.conj q).toMonoidHom =
      K ⊓ centralizer (V : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj q).injective,
      map_conj_of_mem_normalizer hqK,
      map_conj_of_mem_normalizer (normalizer_le_normalizer_centralizer V hqV)]
  have h1 := map_conj_twoGen q (K ⊓ centralizer (V : Set G))
  rw [hX] at h1
  have : q * l * q⁻¹ ∈ (twoGen (K ⊓ centralizer (V : Set G))).map (MulAut.conj q).toMonoidHom :=
    ⟨l, hl, by simp [MulAut.conj_apply]⟩
  rwa [h1] at this

theorem OV_norm [Finite G] (V : Subgroup G) :
    ∀ n ∈ normalizer (V : Set G), ∀ o ∈ OV V, n * o * n⁻¹ ∈ OV V := fun _ hn o ho =>
  (Subgroup.mem_normalizer_iff.1
    (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hn)) o).1 ho

theorem Q₁_le_YV [Finite G] (hG : C3Hyp G) (hS : HYSetup x y K T S V) :
    normalizer (V : Set G) ⊓ (T ⊓ CxK x K) ≤ YV K V := by
  intro q hq
  have hqN : q ∈ normalizer (V : Set G) := hq.1
  have hqC : q ∈ CxK x K := hq.2.2
  have hqK : q ∈ normalizer (K : Set G) := hqC.2.1
  have hLK : lamV K V ≤ K := (twoGen_le _).trans inf_le_left
  refine ⟨hqN, hS.mem_normalizer_HV hG hqN,
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hqN), fun h hh => ?_⟩
  obtain ⟨l, hl, o, ho, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer (lamV_le_normalizer_OV K V)).1 hh
  have e : ⁅l * o, q⁆ = l * ⁅o, q⁆ * l⁻¹ * ⁅l, q⁆ := by simp only [commutatorElement_def]; group
  have h1 : ⁅o, q⁆ ∈ OV V := by
    have : ⁅o, q⁆ = o * (q * o⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact (OV V).mul_mem ho (OV_norm V q hqN _ ((OV V).inv_mem ho))
  have h2 : ⁅l, q⁆ ∈ OV V := by
    have hl2 : ⁅l, q⁆ ∈ lamV K V := by
      have : ⁅l, q⁆ = l * (q * l⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact (lamV K V).mul_mem hl (conj_mem_lamV hqK hqN ((lamV K V).inv_mem hl))
    have hl3 : ⁅l, q⁆ ∈ pPrimeCoreOf 2 K := hqC.2.2.2 l (hLK hl)
    exact hS.lam_inf_OK_le_OV hG ⟨hl2, hl3⟩
  rw [e]
  exact (OV V).mul_mem (OV_norm V l (lamV_le_N K V hl) _ h1) h2

theorem P_sylow_HV [Finite G] (hS : HYSetup x y K T S V) : IsSylowOf 2 (T ⊓ K) (HV K V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLK : lamV K V ≤ K := (twoGen_le _).trans inf_le_left
  have hPL : IsSylowOf 2 (T ⊓ K) (lamV K V) := by
    have h := hS.std.sylow_P
    rw [isSylowOf_iff] at h ⊢
    obtain ⟨-, hp, hdvd⟩ := h
    refine ⟨hS.P_le_lamV, hp, fun h2 => hdvd ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex (T ⊓ K) (lamV K V) K hS.P_le_lamV hLK]
    exact h2.mul_right _
  exact isSylowOf_sup_of_normalizes (lamV_le_normalizer_OV K V)
    (TwoThin.card_pPrimeCoreOf_odd _) hPL

theorem YV_norm [Finite G] (hG : C3Hyp G) (hS : HYSetup x y K T S V) :
    ∀ n ∈ normalizer (V : Set G), ∀ y ∈ YV K V, n * y * n⁻¹ ∈ YV K V := by
  intro n hn y hy
  obtain ⟨hyN, hyH, hyO, hyc⟩ := hy
  have hnyN : n * y * n⁻¹ ∈ normalizer (V : Set G) :=
    (normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).mul_mem hn hyN)
      ((normalizer (V : Set G)).inv_mem hn)
  refine ⟨hnyN, hS.mem_normalizer_HV hG hnyN,
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hnyN), fun k hk => ?_⟩
  have e : ⁅k, n * y * n⁻¹⁆ = n * ⁅n⁻¹ * k * n, y⁆ * n⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact OV_norm V n hn _ (hyc _ (by
    simpa [mul_assoc] using hS.hnormH hG n⁻¹ ((normalizer (V : Set G)).inv_mem hn) k hk))

theorem HV_inf_YV_le_OV [Finite G] (hG : C3Hyp G) (hS : HYSetup x y K T S V) :
    HV K V ⊓ YV K V ≤ OV V := by
  intro d hd
  obtain ⟨hdH, hdN, hdHn, hdO, hdc⟩ := hd
  obtain ⟨l, hl, o, ho, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer (lamV_le_normalizer_OV K V)).1 hdH
  have hlN : l ∈ normalizer (V : Set G) := lamV_le_N K V hl
  have hcomm : ∀ l' ∈ lamV K V, ⁅l', l⁆ ∈ pPrimeCoreOf 2 K := by
    intro l' hl'
    have h1 : ⁅l', l * o⁆ ∈ OV V := hdc l' (Subgroup.mem_sup_left hl')
    have h2 : ⁅l', o⁻¹⁆ ∈ OV V := by
      have : ⁅l', o⁻¹⁆ = l' * o⁻¹ * l'⁻¹ * o := by simp only [commutatorElement_def]; group
      rw [this]
      exact (OV V).mul_mem (OV_norm V l' (lamV_le_N K V hl') _ ((OV V).inv_mem ho)) ho
    have e : ⁅l', l⁆ = ⁅l', l * o⁆ * ((l * o) * ⁅l', o⁻¹⁆ * (l * o)⁻¹) := by
      simp only [commutatorElement_def]; group
    have h3 : ⁅l', l⁆ ∈ OV V := by
      rw [e]
      exact (OV V).mul_mem h1 (OV_norm V (l * o)
        ((normalizer (V : Set G)).mul_mem hlN (HV_le_N K V (Subgroup.mem_sup_right ho))) _ h2)
    have h4 : ⁅l', l⁆ ∈ lamV K V := by
      have : ⁅l', l⁆ = l' * l * l'⁻¹ * l⁻¹ := by simp only [commutatorElement_def]
      rw [this]
      exact (lamV K V).mul_mem ((lamV K V).mul_mem ((lamV K V).mul_mem hl' hl)
        ((lamV K V).inv_mem hl')) ((lamV K V).inv_mem hl)
    exact hS.lam_inf_O_le ⟨h4, h3⟩
  have hlO : l ∈ OV V := hS.lam_inf_OK_le_OV hG ⟨hl, hS.mem_OK_of_comm hl hcomm⟩
  exact (OV V).mul_mem hlO ho

theorem sylow_HY [Finite G] (hG : C3Hyp G) (hS : HYSetup x y K T S V)
    (ha : IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) (YV K V)) :
    IsSylowOf 2 ((T ⊓ K) ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))) (HV K V ⊔ YV K V) := by
  have hHY : HV K V ≤ normalizer ((YV K V : Subgroup G) : Set G) := by
    intro h hh
    have hhN : h ∈ normalizer (V : Set G) := HV_le_N K V hh
    rw [Subgroup.mem_normalizer_iff]
    intro y'
    exact ⟨fun hy => hS.YV_norm hG h hhN y' hy, fun hy => by
      have := hS.YV_norm hG h⁻¹ ((normalizer (V : Set G)).inv_mem hhN) _ hy
      simpa [mul_assoc] using this⟩
  have hinf : Odd (Nat.card ↥(HV K V ⊓ YV K V)) :=
    (TwoThin.card_pPrimeCoreOf_odd _).of_dvd_nat
      (Subgroup.card_dvd_of_le (hS.HV_inf_YV_le_OV hG))
  exact isSylowOf_sup_of_prod hHY hinf hS.P_sylow_HV ha
    (fun a ha b hb => (hS.std.commDisj hS.cen).comm a ha b hb.2)

theorem exists_H_of_sylow [Finite G] (hG : C3Hyp G) (hS : HYSetup x y K T S V) {M : Subgroup G}
    (hKM : K ≤ M) (hO : pPrimeCoreOf 2 (normalizer (V : Set G)) ≤ M)
    (ha : IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) (YV K V)) :
    ∃ H : Subgroup G, H ≤ normalizer (V : Set G) ∧
      (∀ n ∈ normalizer (V : Set G), ∀ h ∈ H, n * h * n⁻¹ ∈ H) ∧ H ≤ M ∧ T ⊓ K ≤ H ∧
      IsSylowOf 2 ((T ⊓ K) ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)))
        (H ⊔ (normalizer (V : Set G) ⊓
          centralizerSection H (pPrimeCoreOf 2 (normalizer (V : Set G))))) :=
  ⟨HV K V, HV_le_N K V, hS.hnormH hG,
    sup_le ((twoGen_le _).trans (inf_le_left.trans hKM)) hO,
    hS.P_le_lamV.trans le_sup_left, hS.sylow_HY hG ha⟩

theorem YV_le_M_of_le [Finite G] (hstd : Th2Std x y K T S)
    (hVQ : V ≤ T ⊓ CxK x K) (hPle : T ⊓ K ≤ lamV K V) {M U : Subgroup G}
    (hO : OV V ≤ M) (hUP : U ≤ T ⊓ K)
    (hFM : normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M) : YV K V ≤ M := by
  intro y hy
  obtain ⟨hyN, hyc⟩ := hy
  have hycomm : ∀ k ∈ HV K V, ⁅k, y⁆ ∈ OV V := hyc.2.2
  have hUH : U ≤ HV K V := hUP.trans (hPle.trans le_sup_left)
  have hFT : U ⊔ V ≤ T := sup_le (hUP.trans inf_le_left) (hVQ.trans inf_le_left)
  have hF2 : IsPGroup 2 ↥(U ⊔ V) := hstd.T_pGroup.to_le hFT
  have hFN : U ⊔ V ≤ normalizer (V : Set G) :=
    sup_le (hUH.trans (HV_le_N K V)) Subgroup.le_normalizer
  have hVnorm : ∀ n ∈ normalizer (V : Set G), ∀ v ∈ V, n * v * n⁻¹ ∈ V := fun n hn v hv =>
    (Subgroup.mem_normalizer_iff.1 hn v).1 hv
  refine Th2.P812.mem_of_normalizes_sup hFN hF2 hFM hO (y := y) (fun f hf => ?_)
  have hle : (U ⊔ V).map (MulAut.conj y).toMonoidHom ≤ (U ⊔ V) ⊔ OV V := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      have h1 : ⁅u, y⁆ ∈ OV V := hycomm u (hUH hu)
      have e : (MulAut.conj y).toMonoidHom u = (⁅u, y⁆)⁻¹ * u := by
        change y * u * y⁻¹ = (⁅u, y⁆)⁻¹ * u
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((OV V).inv_mem h1))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu))
    · rintro _ ⟨v, hv, rfl⟩
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hVnorm y hyN v hv))
  exact hle ⟨f, hf, by simp [MulAut.conj_apply]⟩

theorem YV_le_M [Finite G] (hS : HYSetup x y K T S V) {M U : Subgroup G}
    (hO : OV V ≤ M) (hU : IsFourSub (T ⊓ K) U)
    (hFM : normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M) : YV K V ≤ M :=
  YV_le_M_of_le hS.std hS.hVQ hS.P_le_lamV hO hU.1 hFM

end HYSetup

end CFSG.GH74.GLS.Th2.HY
