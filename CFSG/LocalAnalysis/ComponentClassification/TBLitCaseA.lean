module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitLift

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem caseA_star (hI : TBInputs) (hX : TBSetting X) {a b γ : X} {S E : Subgroup X}
    (hC : CoreConfig a b γ S E) {M : Subgroup X} (hM : M ≤ centralizer ({γ} : Set X))
    (hMc : IsPComponent 2 (M.subgroupOf (centralizer ({γ} : Set X))))
    (hSK : S ≤ M ⊔ conjugate M b)
    (hSKc : IsPComponent 2 (S.subgroupOf ((M ⊔ conjugate M b) ⊓ centralizer ({b} : Set X))))
    (haM : a ∈ normalizer (M : Set X)) (hEM : E ≤ normalizer (M : Set X))
    (hanM : ¬ ∀ m ∈ M, ⁅m, a⁆ ∈ oddCoreIn M) (henM : ∃ e ∈ E, ¬ ∀ m ∈ M, ⁅m, e⁆ ∈ oddCoreIn M)
    (heq : M = conjugate M b) :
    ∃ (δ₁ δ₂ : X) (N₁ N₂ E' : Subgroup X), StarConfig a δ₁ δ₂ N₁ N₂ E' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hX.simple
  obtain ⟨p, n, hpf, hp2, hn, ⟨eS⟩⟩ := hC.hSL
  have hMM : M ⊔ conjugate M b = M := by rw [← heq, sup_idem]
  have hSM : S ≤ M := by
    rw [hMM] at hSK
    exact hSK
  have hSMc : IsPComponent 2 (S.subgroupOf (M ⊓ centralizer ({b} : Set X))) := by
    rw [hMM] at hSKc
    exact hSKc
  have hbM : b ∈ normalizer (M : Set X) := by
    rw [mem_normalizer_iff]
    intro h
    have h1 := SetLike.ext_iff.mp heq h
    rw [UnbalancedLayer.mem_conjugate_iff] at h1
    exact h1
  have hconf : IsUnbalancingConfig γ a M E :=
    isUnbalancingConfig_of_actsProperly hC.hγ hC.ha hC.haγ hM hMc hC.hEa
      (hC.hE.trans inf_le_right) haM hEM hSM hC.hprop
  have hγM : γ ∈ M := hSM hC.hγS
  rcases intrinsic_config_types hI hX hconf hγM with ⟨hodd, hnot⟩ | hL34
  swap
  ·
    exact absurd hC.hprop (hI.l34 X hX.nonab hX.kProper hX.unbalanced hX.notU a b γ hC.ha hC.hb
      hC.hγ hC.hab hC.haγ hC.hbγ M hM hMc hγM haM hbM hL34 S hSM hC.hS hC.hSc hC.hγS hC.hSL E
      hC.hEa hC.hE)
  by_cases hbt : ∀ m ∈ M, ⁅m, b⁆ ∈ oddCoreIn M
  ·
    exact (fixedLayer_SL2_false hI hX hC.hγ hC.hb hC.hbγ hM hMc hbM hbt hC.hS hC.hSc hSM hSMc
      hC.hγS hp2 hn eS).elim
  obtain ⟨u, hu2, S₁, S₂, hS₁, hS₁c, hS₂, hS₂c, ⟨p', n', hpf', hp2', hn', ⟨e₁⟩, ⟨e₂⟩⟩, hS12,
    hS12', hcen, ha₁, ha₂, hE₁, hE₂, hant₁, hant₂, hent₁, hent₂⟩ :=
    caseA_propB hI hC hSM hSMc haM hEM hbM hbt hanM henM hconf hodd hnot
  obtain ⟨c, hcdef⟩ : ∃ c : M ⧸ pPrimeCore 2 M, c = ((⟨γ, hγM⟩ : M) : M ⧸ pPrimeCore 2 M) :=
    ⟨_, rfl⟩
  have hcen' : (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c := by
    rw [hcdef]
    exact hcen
  have ha2 : a * a = 1 := by rw [← pow_two, ← hC.ha, pow_orderOf_eq_one]
  have hγγ : γ * γ = 1 := by rw [← pow_two, ← hC.hγ, pow_orderOf_eq_one]
  have hcZ : ∀ q : M ⧸ pPrimeCore 2 M, c * q = q * c := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hcdef, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hM m.2)).symm
  have hc2 : c ^ 2 = 1 := by
    rw [hcdef, ← QuotientGroup.mk_pow]
    have h1 : (⟨γ, hγM⟩ : M) ^ 2 = 1 := Subtype.ext (by
      change γ ^ 2 = 1
      rw [pow_two]
      exact hγγ)
    rw [h1, QuotientGroup.mk_one]
  have huu : u ^ 2 = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu2] at h
  have huc : u * c = c * u := (hcZ u).symm
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu2
    omega
  obtain ⟨z₁, hz₁S, -, hz₁1, hz₁c, hz₁u⟩ := exists_central_involution hp2' hn' e₁
  obtain ⟨z₂, hz₂S, -, hz₂1, hz₂c, hz₂u⟩ := exists_central_involution hp2' hn' e₂
  have hS₁₂ : S₁ ≤ centralizer (S₂ : Set (M ⧸ pPrimeCore 2 M)) :=
    commutator_eq_bot_iff_le_centralizer.mp hS12
  have hzV : ∀ z, (z ∈ S₁ ∧ ∀ x ∈ S₁, z * x = x * z) ∨ (z ∈ S₂ ∧ ∀ x ∈ S₂, z * x = x * z) →
      z ∈ zpowers u ⊔ zpowers c := by
    intro z hz
    rw [← hcen']
    have hle : S₁ ⊔ S₂ ≤ centralizer ({z} : Set (M ⧸ pPrimeCore 2 M)) := by
      rcases hz with ⟨hzS, hzc⟩ | ⟨hzS, hzc⟩
      · refine sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (hzc y hy).symm) ?_
        intro y hy
        rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.mp (hS₁₂ hzS) y hy
      · refine sup_le ?_ (fun y hy => mem_centralizer_singleton_iff.mpr (hzc y hy).symm)
        intro y hy
        rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.mp (hS₁₂ hy) z hzS).symm
    have hzmem : z ∈ S₁ ⊔ S₂ := by
      rcases hz with ⟨hzS, -⟩ | ⟨hzS, -⟩
      · exact mem_sup_left hzS
      · exact mem_sup_right hzS
    exact ⟨⟨z, hzmem⟩, mem_center_iff.mpr fun g =>
      Subtype.ext (mem_centralizer_singleton_iff.mp (hle g.2)), rfl⟩
  have hz₁V := eq_of_mem_sup_zpowers huu hc2 huc (hzV z₁ (.inl ⟨hz₁S, hz₁c⟩))
  have hz₂V := eq_of_mem_sup_zpowers huu hc2 huc (hzV z₂ (.inr ⟨hz₂S, hz₂c⟩))
  have hz12 : z₁ ≠ z₂ := by
    intro h
    have h1 : z₁ ∈ S₁ ⊓ S₂ := mem_inf.mpr ⟨hz₁S, by rw [h]; exact hz₂S⟩
    rw [hS12', mem_bot] at h1
    exact hz₁1 h1
  have hφa2 : ∀ q, oddQuotAction M ⟨a, haM⟩ (oddQuotAction M ⟨a, haM⟩ q) = q := by
    intro q
    rw [oddQuotAction_mul_apply,
      show (⟨a * a, mul_mem haM haM⟩ : normalizer (M : Set X)) = 1 from Subtype.ext ha2,
      map_one, MulAut.one_apply]
  have hfz₁ := fixed_of_unique_central hz₁S hz₁1 hz₁c hz₁u (oddQuotAction M ⟨a, haM⟩) ha₁ hφa2
  have hfz₂ := fixed_of_unique_central hz₂S hz₂1 hz₂c hz₂u (oddQuotAction M ⟨a, haM⟩) ha₂ hφa2
  have hfu : oddQuotAction M ⟨a, haM⟩ u = u := by
    rcases mem_triple_of_klein hc2 huc hz₁V hz₂V hz₁1 hz₂1 hz12 with h | h | h
    · rw [← h]
      exact hfz₁
    · rw [← h]
      exact hfz₂
    · rw [← h, map_mul, hfz₁, hfz₂]
  obtain ⟨mu, hmu⟩ := QuotientGroup.mk_surjective u
  have hOMn : ((oddCoreIn M).subgroupOf M).Normal := by
    rw [show (oddCoreIn M).subgroupOf M = pPrimeCore 2 M from
      comap_map_eq_self_of_injective M.subtype_injective _]
    infer_instance
  have ha2' : a ^ 2 = 1 := by rw [pow_two]; exact ha2
  have hamu : a * (mu : X) * a⁻¹ ∈ M := (mem_normalizer_iff.mp haM _).mp mu.2
  obtain ⟨δ, hδM, hδ2, hδa, hδmu⟩ := exists_involution_lift (oddCoreIn_le M) hOMn
    (odd_card_oddCoreIn M) ha2' (normalizer_le_normalizer_oddCoreIn M haM) mu.2
    (by
      have h1 : ((mu ^ 2 : M) : X) ∈ oddCoreIn M := by
        rw [mem_oddCoreIn_iff_mk, QuotientGroup.mk_pow, hmu, huu]
      exact h1)
    (by
      intro h
      apply hu1
      rw [← hmu, ← mem_oddCoreIn_iff_mk]
      exact h)
    (by
      have h2 : ((⟨a * mu * a⁻¹, hamu⟩ : M) : M ⧸ pPrimeCore 2 M) =
          oddQuotAction M ⟨a, haM⟩ u := by
        rw [← hmu, oddQuotAction_mk]
      have h1 : ((mu⁻¹ * ⟨a * mu * a⁻¹, hamu⟩ : M) : X) ∈ oddCoreIn M := by
        rw [mem_oddCoreIn_iff_mk, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h2, hfu, hmu,
          inv_mul_cancel]
      exact h1)
  have hδu : ((⟨δ, hδM⟩ : M) : M ⧸ pPrimeCore 2 M) = u := by
    have h1 : (((⟨δ, hδM⟩ : M)⁻¹ * mu : M) : X) ∈ oddCoreIn M := hδmu
    rw [mem_oddCoreIn_iff_mk, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmu,
      inv_mul_eq_one] at h1
    exact h1
  have hδδ : δ * δ = 1 := by rw [← pow_two, ← hδ2, pow_orderOf_eq_one]
  have hδγ : δ * γ = γ * δ := mem_centralizer_singleton_iff.mp (hM hδM)
  have hδaC : δ ∈ centralizer ({a} : Set X) := mem_centralizer_singleton_iff.mpr hδa
  have hS₁δ : S₁ ≤ centralizer ({((⟨δ, hδM⟩ : M) : M ⧸ pPrimeCore 2 M)} : Set _) := by
    rw [hδu]
    exact hS₁
  have hS₁δc : IsPComponent 2 (S₁.subgroupOf
      (centralizer ({((⟨δ, hδM⟩ : M) : M ⧸ pPrimeCore 2 M)} : Set _))) := by
    rw [hδu]
    exact hS₁c
  have hS₂δ : S₂ ≤ centralizer ({((⟨δ, hδM⟩ : M) : M ⧸ pPrimeCore 2 M)} : Set _) := by
    rw [hδu]
    exact hS₂
  have hS₂δc : IsPComponent 2 (S₂.subgroupOf
      (centralizer ({((⟨δ, hδM⟩ : M) : M ⧸ pPrimeCore 2 M)} : Set _))) := by
    rw [hδu]
    exact hS₂c
  obtain ⟨N₁, -, hN₁, hN₁c, hN₁q, eN₁, hprop₁⟩ := lift_component hC.ha hM hMc hδM hδδ hδa haM
    hC.hEa hEM hS₁δ hS₁δc hp2' hn' e₁ ha₁ hE₁ hant₁ hent₁
  obtain ⟨N₂, -, hN₂, hN₂c, hN₂q, eN₂, hprop₂⟩ := lift_component hC.ha hM hMc hδM hδδ hδa haM
    hC.hEa hEM hS₂δ hS₂δc hp2' hn' e₂ ha₂ hE₂ hant₂ hent₂
  have hlift : ∀ z : M ⧸ pPrimeCore 2 M, z ≠ 1 → (z = 1 ∨ z = u ∨ z = c ∨ z = u * c) →
      ∃ w : X, (w = δ ∨ w = γ ∨ w = δ * γ) ∧
        ∃ hw : w ∈ M, ((⟨w, hw⟩ : M) : M ⧸ pPrimeCore 2 M) = z := by
    intro z hz1 hz
    rcases hz with h | h | h | h
    · exact absurd h hz1
    · exact ⟨δ, .inl rfl, hδM, hδu.trans h.symm⟩
    · exact ⟨γ, .inr (.inl rfl), hγM, by rw [h, hcdef]⟩
    · refine ⟨δ * γ, .inr (.inr rfl), mul_mem hδM hγM, ?_⟩
      rw [h, ← hδu, hcdef]
      rfl
  obtain ⟨w₁, hw₁, hw₁M, hw₁z⟩ := hlift z₁ hz₁1 hz₁V
  obtain ⟨w₂, hw₂, hw₂M, hw₂z⟩ := hlift z₂ hz₂1 hz₂V
  have hw12 : w₁ ≠ w₂ := by
    intro h
    subst h
    exact hz12 (hw₁z.symm.trans hw₂z)
  have hCC := centralizer_inf_eq_of_mem_triple hδδ hγγ hw₁ hw₂ hw12
  have hord : ∀ {w : X} (hw : w = δ ∨ w = γ ∨ w = δ * γ) (hwM : w ∈ M) {z},
      ((⟨w, hwM⟩ : M) : M ⧸ pPrimeCore 2 M) = z → z ≠ 1 → orderOf w = 2 := by
    intro w hw hwM z hwz hz1
    refine orderOf_eq_prime (sq_eq_one_of_mem_triple hδδ hγγ hδγ hw) ?_
    rintro rfl
    exact hz1 (hwz.symm.trans (QuotientGroup.mk_one (pPrimeCore 2 M)))
  have hcomm : ∀ {w : X}, (w = δ ∨ w = γ ∨ w = δ * γ) → ∀ {N : Subgroup X},
      N ≤ centralizer ({γ} : Set X) ⊓ centralizer ({δ} : Set X) → ∀ x ∈ N, x * w = w * x :=
    fun hw N hN x hx => (commute_triple_of_commute hw
      (show Commute x δ from mem_centralizer_singleton_iff.mp (mem_inf.mp (hN hx)).2)
      (show Commute x γ from mem_centralizer_singleton_iff.mp (mem_inf.mp (hN hx)).1)).eq
  have hwN₁ : w₁ ∈ N₁ := mem_of_mem_quotImage hw₁M (sq_eq_one_of_mem_triple hδδ hγγ hδγ hw₁)
    (hcomm hw₁ hN₁) (by rw [hN₁q, hw₁z]; exact hz₁S)
  have hwN₂ : w₂ ∈ N₂ := mem_of_mem_quotImage hw₂M (sq_eq_one_of_mem_triple hδδ hγγ hδγ hw₂)
    (hcomm hw₂ hN₂) (by rw [hN₂q, hw₂z]; exact hz₂S)
  have haδ : Commute a δ := (show Commute δ a from hδa).symm
  have haγ : Commute a γ := hC.haγ
  have hFγ : E ⊔ conjugate E δ ≤ centralizer ({γ} : Set X) :=
    sup_le (hC.hE.trans inf_le_right) (conjugate_le_of_le_of_mem (hC.hE.trans inf_le_right)
      (mem_centralizer_singleton_iff.mpr hδγ))
  refine ⟨w₁, w₂, N₁, N₂, (E ⊔ conjugate E δ) ⊓ centralizer ({δ} : Set X),
    ⟨hC.ha, hord hw₁ hw₁M hw₁z hz₁1, hord hw₂ hw₂M hw₂z hz₂1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwN₁,
      hwN₂, ⟨p', n', hpf', hp2', hn', eN₁, eN₂⟩, ?_, ?_, hprop₁, hprop₂⟩⟩
  · exact (commute_triple_of_commute hw₂ (commute_of_mem_triple hδγ hw₁).1
      (commute_of_mem_triple hδγ hw₁).2).eq
  · exact (commute_triple_of_commute hw₁ haδ haγ).eq
  · exact (commute_triple_of_commute hw₂ haδ haγ).eq
  · rw [hCC]
    exact hN₁
  · rw [hCC]
    exact hN₁c
  · rw [hCC]
    exact hN₂
  · rw [hCC]
    exact hN₂c
  · exact inf_le_left.trans (sup_le hC.hEa (conjugate_le_oddCentralizerCore hδaC hC.hEa))
  · rw [hCC]
    exact le_inf (inf_le_left.trans hFγ) inf_le_right

end CFSG.ComponentClassification.TBLit
