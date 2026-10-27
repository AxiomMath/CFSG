module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10Cls
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81ConfK

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4

namespace X10

variable {K : Type} [Field K]

theorem mul_self_eq_negS {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = p ^ f) (A : gsp 2 K) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K)
    {Z : StatedSp 2 K} (hZf : Z ∈ fixOf (conjSp 2 K A)) (hZZ : proj 2 K Z * proj 2 K Z = 1)
    (hZ1 : proj 2 K Z ≠ 1) : Z * Z = negS K := by
  have hs : Z * Z ∈ spScalars 2 K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul]
    exact hZZ
  rcases (mem_spScalars_iff _).mp hs with h | h
  · exfalso
    have h1 : Z * Z = 1 := sp_ext (by rw [h]; rfl)
    exact hZ1 (ConfP.proj_eq_one_of
      (ConfP.fixOf_eq_one_or_negS hp hp2 hf hK A hd0 hdsq hAA hμ hZf h1))
  · exact eq_negS_of_coe h

theorem tauZ_equiv_u1 {K₀ : Type} [Group K₀] [Finite K₀] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK₀ : Blueprint.LieModel K₀ .PSp 2 p f) (c : Cat8.QConf K₀ (p ^ f))
    (hc : c.Props) {tτ tz : K₀} (hτ : MulAut.conj tτ = c.tau) (hz : MulAut.conj tz = c.z) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : K₀ ≃* StatedProj (StatedSp 2 K)),
      Nat.card K = p ^ f ∧ φ (tτ * tz) = u1 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut K₀) := Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀))
    (fun φ ψ h => MulEquiv.ext (congrFun h))
  have hF := ConfK.facts_psp hp hp2 hf hK₀ c.a c.adm
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hK₀
  obtain ⟨hsimp, u, w, huw⟩ := cfSec8Simple K₀ p f hp hp2 hf (Or.inl hK₀)
  have hcz : ∀ z : K₀, z ∈ center K₀ → z = 1 := by
    intro z hz
    have hn : (center K₀).Normal := inferInstance
    rcases hn.eq_bot_or_eq_top with h | h
    · rw [h, mem_bot] at hz
      exact hz
    · exfalso
      have hu : u ∈ center K₀ := h ▸ mem_top u
      exact huw (mem_center_iff.mp hu w).symm
  have hinj : Function.Injective (MulAut.conj : K₀ →* MulAut K₀) :=
    fun g h hgh => conj_injective_of_center hcz hgh
  have hcommG : ∀ β : MulAut K₀, ∀ x, e (β x) = MulAut.congr e β (e x) := fun β x => by
    simp [MulAut.congr_apply]
  have hfixc : ∀ β : MulAut K₀,
      Nat.card (fixOf (MulAut.congr e β)) = Nat.card (Eight.fixSubgroup β) := by
    intro β
    rw [← map_fixOf_of_comm (hcommG β), ← Nat.card_congr ((fixOf β).equivMapOfInjective _
      e.injective).toEquiv]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have hout : MulAut.congr e c.a ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range := by
    rintro ⟨y, hy⟩
    apply c.adm.out
    refine ⟨e.symm y, ?_⟩
    ext x
    apply e.injective
    rw [hcommG c.a, ← hy]
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨A, hA, d, hd0, hdsq, hAA, hμ⟩ := exists_typeII_of_admissible hp hp2 hf hK
    (MulAut.congr e c.a) (by rw [← map_mul, c.adm.sq, map_one]) hout
    (by rw [hfixc]; exact c.adm.dvd)
  obtain ⟨hQ, -⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A hd0 hdsq hAA hμ
  have hθα : ∀ g, MulAut.congr e c.a (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
    rw [hA, conjAut_proj]
  have heq := L0Psp.commutator_fixOf_eq (conjSp 2 K A) hθα hQ.1
  have hL0 : Cat8.L0 K₀ c.a = (⁅fixOf c.a, fixOf c.a⁆).map (MulAut.conj : K₀ →* MulAut K₀) := by
    show ⁅Cat8.Inn K₀ ⊓ centralizer ({c.a} : Set (MulAut K₀)),
      Cat8.Inn K₀ ⊓ centralizer ({c.a} : Set (MulAut K₀))⁆ = _
    rw [← map_conj_fixOf hcz c.a, Subgroup.map_commutator]
  have hcomm' : (⁅fixOf c.a, fixOf c.a⁆ : Subgroup K₀).map e.toMonoidHom =
      (fixOf (conjSp 2 K A)).map (proj 2 K) := by
    rw [Subgroup.map_commutator, map_fixOf_of_comm (hcommG c.a), heq]
  have hQC := c.Q_le
  have hQS := c.Q_sylow
  have hQ2 : IsPGroup 2 c.Q := by
    obtain ⟨T, hT⟩ := hQS
    have h := T.isPGroup'
    rw [hT] at h
    exact h.of_equiv (subgroupOfEquivOfLe hQC)
  have hQa : ∀ w ∈ c.Q, w * c.a = c.a * w := fun w hw =>
    mem_centralizer_singleton_iff.mp (hQC hw).2
  have hIn : (Cat8.Inn K₀).Normal := ConfA.inn_normal K₀
  have hLfix : Cat8.L0 K₀ c.a ≤ Cat8.innFix K₀ c.a := ConfA.commutator_self_le _
  have hfixC : Cat8.innFix K₀ c.a ≤ Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)) :=
    inf_le_inf_right _ le_sup_left
  have hLC := hLfix.trans hfixC
  have hLn : ∀ x ∈ Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)),
      ∀ y ∈ Cat8.L0 K₀ c.a, x * y * x⁻¹ ∈ Cat8.L0 K₀ c.a := by
    intro x hx y hy
    refine ConfA.conj_mem_commutator (fun w hw => ?_) hy
    refine ⟨hIn.conj_mem _ hw.1 x, mem_centralizer_singleton_iff.mpr ?_⟩
    have hxa : x * c.a = c.a * x := mem_centralizer_singleton_iff.mp hx.2
    have hwa : w * c.a = c.a * w := mem_centralizer_singleton_iff.mp hw.2
    have hxa' : x⁻¹ * c.a = c.a * x⁻¹ := by
      calc x⁻¹ * c.a = x⁻¹ * (c.a * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * c.a) * x⁻¹ := by rw [hxa]
        _ = c.a * x⁻¹ := by group
    calc x * w * x⁻¹ * c.a = x * w * (x⁻¹ * c.a) := by group
      _ = x * (w * c.a) * x⁻¹ := by rw [hxa']; group
      _ = x * (c.a * w) * x⁻¹ := by rw [hwa]
      _ = x * c.a * w * x⁻¹ := by group
      _ = c.a * (x * w * x⁻¹) := by rw [hxa]; group
  have hDcard : Nat.card c.D = 2 ^ (Cat8.ordL2 ((p ^ f) ^ 2)).factorization 2 := by
    rw [← hF.card_L0]
    exact ConfA.card_inf_eq hQC hLC hLn hQS
  have hDQ : c.D ≤ c.Q := inf_le_left
  obtain ⟨hZ2, t, htD, htt, httc⟩ := hF.dihedral c.D inf_le_right (hQ2.to_le hDQ) hDcard
  have hzt : c.z = t * t := by
    have hzZ : c.z ∈ c.D ⊓ centralizer (c.D : Set (MulAut K₀)) :=
      ⟨c.z_mem, mem_centralizer_iff.mpr fun x hx => (c.z_comm x hx).symm⟩
    have httZ : t * t ∈ c.D ⊓ centralizer (c.D : Set (MulAut K₀)) := ⟨mul_mem htD htD, httc⟩
    obtain ⟨y, -, hyu⟩ :=
      (Nat.card_eq_two_iff' (1 : ↥(c.D ⊓ centralizer (c.D : Set (MulAut K₀))))).mp hZ2
    have e1 : (⟨c.z, hzZ⟩ : ↥(c.D ⊓ centralizer (c.D : Set (MulAut K₀)))) = y :=
      hyu _ (fun h => c.z_ne (congrArg Subtype.val h))
    have e2 : (⟨t * t, httZ⟩ : ↥(c.D ⊓ centralizer (c.D : Set (MulAut K₀)))) = y :=
      hyu _ (fun h => htt (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have htL : t ∈ (⁅fixOf c.a, fixOf c.a⁆ : Subgroup K₀).map (MulAut.conj : K₀ →* MulAut K₀) :=
    hL0 ▸ htD.2
  obtain ⟨tw, htwC, htw⟩ := htL
  have hWe : e tw ∈ (fixOf (conjSp 2 K A)).map (proj 2 K) :=
    hcomm' ▸ mem_map_of_mem e.toMonoidHom htwC
  obtain ⟨W, hWf, hW⟩ := hWe
  have hztw : tz = tw * tw := hinj (by rw [hz, hzt, map_mul, htw])
  have hz2 : tz * tz = 1 := hinj (by rw [map_mul, hz, c.z_sq, map_one])
  have hz1 : tz ≠ 1 := fun h => c.z_ne (by rw [← hz, h, map_one])
  have hZe : proj 2 K (W * W) = e tz := by rw [map_mul, hW, hztw, map_mul]
  have hZZ : proj 2 K (W * W) * proj 2 K (W * W) = 1 := by rw [hZe, ← map_mul, hz2, map_one]
  have hZ1 : proj 2 K (W * W) ≠ 1 := by
    rw [hZe]
    exact fun h => hz1 (e.injective (h.trans (map_one e).symm))
  have hZn := mul_self_eq_negS hp hp2 hf hK A hd0 hdsq hAA hμ (mul_mem hWf hWf) hZZ hZ1
  obtain ⟨T, hT⟩ := proj_surjective (e tτ)
  have htc : tτ * tw = tw * tτ := hinj (by
    rw [map_mul, map_mul, hτ, htw]
    exact hc.tau_comm t (hDQ htD))
  have hTW : proj 2 K T * proj 2 K W = proj 2 K W * proj 2 K T := by
    rw [hT, hW, ← map_mul, ← map_mul, htc]
  have hnc : ∀ x : StatedSp 2 K, x * negS K = negS K * x := fun x =>
    mem_center_iff.mp (mem_center_of_mem_spScalars
      ((mem_spScalars_iff _).mpr (Or.inr coe_negS))) x
  have hTT : T * T = negS K := by
    obtain ⟨k, ⟨tk, rfl⟩, hk⟩ := hc.z_tau
    have hk' : tk⁻¹ * tz * tk = tτ := hinj (by rw [map_mul, map_mul, map_inv, hz, hτ, hk])
    obtain ⟨G, hG⟩ := proj_surjective (e tk)
    have hpT : proj 2 K T = proj 2 K (G⁻¹ * (W * W) * G) := by
      rw [hT, ← hk', map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hG, hZe]
    have hs : T⁻¹ * (G⁻¹ * (W * W) * G) ∈ spScalars 2 K := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hpT, inv_mul_cancel]
    set s := T⁻¹ * (G⁻¹ * (W * W) * G) with hsdef
    have hsc : ∀ x : StatedSp 2 K, x * s = s * x := fun x =>
      mem_center_iff.mp (mem_center_of_mem_spScalars hs) x
    have hss : s * s = 1 := by
      rcases (mem_spScalars_iff _).mp hs with h | h
      · rw [sp_ext (x := s) (y := 1) (by rw [h]; rfl), one_mul]
      · rw [eq_negS_of_coe h, ConfP.negS_mul_self]
    have h1 : G⁻¹ * (W * W) * G = T * s := by rw [hsdef]; group
    calc T * T = T * T * (s * s) := by rw [hss, mul_one]
      _ = T * (T * s) * s := by group
      _ = T * (s * T) * s := by rw [hsc T]
      _ = T * s * (T * s) := by group
      _ = G⁻¹ * (W * W * (W * W)) * G := by rw [← h1]; group
      _ = negS K := by rw [hZn, mul_assoc, ← hnc G, ← mul_assoc, inv_mul_cancel, one_mul]
  have hTn : proj 2 K T ∉ (fixOf (conjSp 2 K A)).map (proj 2 K) := by
    intro hmem
    rw [← hcomm', hT] at hmem
    obtain ⟨x, hx, hxe⟩ := hmem
    have hxt : x = tτ := e.injective hxe
    have hτL : c.tau ∈ Cat8.L0 K₀ c.a := by
      rw [hL0, ← hτ, ← hxt]
      exact mem_map_of_mem _ hx
    have hτD : c.tau ∈ c.D := ⟨by rw [hc.Q_eq]; exact mem_sup_left (mem_sup_right
      (mem_zpowers _)), hτL⟩
    have hQeq : c.Q = c.D ⊔ zpowers c.a := by
      rw [hc.Q_eq, sup_eq_left.mpr (zpowers_le.mpr hτD)]
    have haD : c.a ∉ c.D := fun h => c.adm.out ((inf_le_right.trans
      (hLfix.trans inf_le_left)) h)
    have hBN : zpowers c.a ≤ normalizer (c.D : Set (MulAut K₀)) := by
      rw [zpowers_le]
      refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · rw [← hQa x (hDQ hx), mul_inv_cancel_right]
        exact hx
      · have h1 := hQa _ (hDQ hx)
        have hxy : x = c.a * x * c.a⁻¹ := by
          calc x = c.a⁻¹ * (c.a * x * c.a⁻¹ * c.a) := by group
            _ = c.a⁻¹ * (c.a * (c.a * x * c.a⁻¹)) := by rw [h1]
            _ = c.a * x * c.a⁻¹ := by group
        rw [hxy]
        exact hx
    have hdisj : Disjoint c.D (zpowers c.a) := by
      rw [disjoint_iff, eq_bot_iff]
      intro y hy
      obtain ⟨hyD, hya⟩ := mem_inf.mp hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hya
      rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [← two_mul, _root_.zpow_mul, zpow_two, c.adm.sq, _root_.one_zpow]
        exact one_mem _
      · exfalso
        apply haD
        have h1 : c.a ^ (2 * j + 1) = c.a := by
          rw [_root_.zpow_add, _root_.zpow_mul, zpow_two, c.adm.sq, _root_.one_zpow, one_mul,
            zpow_one]
        rwa [h1] at hyD
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer c.D
      (zpowers c.a) hBN hdisj
    have ha2 : Nat.card (zpowers c.a) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact c.adm.sq) fun h =>
        c.adm.out (h ▸ one_mem _)
    have h4 := hc.card_Q
    rw [hQeq, hcard, ha2] at h4
    have h8 := hc.eight_le
    omega
  obtain ⟨g, hg⟩ := exists_conj_T1_mul hp hp2 hf hK A hd0 hdsq hAA hμ hTT hWf hTW hTn hZZ hZ1
  refine ⟨K, inferInstance, inferInstance, e.trans (MulAut.conj (proj 2 K g)⁻¹), hK, ?_⟩
  rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv, map_mul, ← hT, ← hZe, ← map_inv,
    ← map_mul, ← map_mul, ← map_mul, hg]
  rfl

end X10

end CFSG.ComponentClassification.GSThmB
