module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGInvolution
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X]

theorem isPGroup_quot_iff {A : Subgroup X} :
    IsPGroup 2 (↥A ⧸ pPrimeCore 2 ↥A) ↔
      ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ (pPrimeCore 2 ↥A).map A.subtype := by
  constructor
  · intro hA a ha
    obtain ⟨k, hk⟩ := hA (QuotientGroup.mk ⟨a, ha⟩)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    exact ⟨k, ⟨_, hk, rfl⟩⟩
  · intro hA g
    obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, ⟨y, hy, hya⟩⟩ := hA a ha
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : (⟨a, ha⟩ : ↥A) ^ 2 ^ k = y := Subtype.ext (by rw [Subgroup.coe_pow]; exact hya.symm)
    rwa [this]

theorem isPGroup_quot_of_le [Finite X] {A B : Subgroup X} (hBA : B ≤ A)
    (hA : IsPGroup 2 (↥A ⧸ pPrimeCore 2 ↥A)) : IsPGroup 2 (↥B ⧸ pPrimeCore 2 ↥B) := by
  rw [isPGroup_quot_iff] at hA ⊢
  intro b hb
  obtain ⟨k, hk⟩ := hA b (hBA hb)
  refine ⟨k, le_map_pPrimeCore inf_le_right (fun a ha n hn =>
    ⟨conj_mem_map_pPrimeCore_self (hBA ha) hn.1, B.mul_mem (B.mul_mem ha hn.2) (B.inv_mem ha)⟩)
    (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) (coprime_card_map_pPrimeCore _))
    ⟨hk, B.pow_mem hb _⟩⟩

theorem isPGroup_quot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : IsPGroup 2 (A ⧸ pPrimeCore 2 A)) : IsPGroup 2 (B ⧸ pPrimeCore 2 B) :=
  hA.of_equiv (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e))

theorem isPGroup_quot_of_isCyclic {Q : Type*} [Group Q] [Finite Q] (P : Sylow 2 Q)
    (hP : IsCyclic P) : IsPGroup 2 (Q ⧸ pPrimeCore 2 Q) := by
  by_cases hev : 2 ∣ Nat.card Q
  · have hmin : (Nat.card Q).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr hev
    have hc := IsCyclic.isComplement' hmin hP
    have hNodd : Nat.Coprime 2 (Nat.card
        (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hmin)).ker) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (MonoidHom.not_dvd_card_ker_transferSylow P _)
    have hNle : (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hmin)).ker ≤
        pPrimeCore 2 Q := le_sSup ⟨MonoidHom.normal_ker _, hNodd⟩
    have hdvd := Subgroup.index_dvd_of_le hNle
    rw [hc.symm.index_eq_card] at hdvd
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn] at hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card hm
  · have htop : (⊤ : Subgroup Q) ≤ pPrimeCore 2 Q := le_sSup ⟨normal_top,
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by rwa [Subgroup.card_top])⟩
    intro g
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨0, by rw [pow_zero, pow_one, QuotientGroup.eq_one_iff]; exact htop (mem_top q)⟩

variable [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

theorem isPGroup_quot_of_rho (h : Standing t L p f) {A : Subgroup X}
    (hAH : A ≤ centralizer ({t} : Set X)) (htA : t ∈ A)
    (hA : IsPGroup 2 (↥((A.subgroupOf (centralizer ({t} : Set X))).map h.rho) ⧸
      pPrimeCore 2 ↥((A.subgroupOf (centralizer ({t} : Set X))).map h.rho))) :
    IsPGroup 2 (↥A ⧸ pPrimeCore 2 ↥A) := by
  set H := centralizer ({t} : Set X) with hH
  set B := (A.subgroupOf H).map h.rho with hB
  set OB := (pPrimeCore 2 ↥B).map B.subtype with hOB
  set Q : Subgroup X := A ⊓ (OB.comap h.rho).map H.subtype with hQ
  have hQA : Q ≤ A := inf_le_left
  have hmemQ : ∀ {a : X} (ha : a ∈ A), a ∈ Q ↔ h.rho ⟨a, hAH ha⟩ ∈ OB := by
    intro a ha
    constructor
    · rintro ⟨-, ⟨b, hb, hba⟩⟩
      have : b = ⟨a, hAH ha⟩ := Subtype.ext hba
      rwa [← this]
    · intro hρ
      exact ⟨ha, ⟨⟨a, hAH ha⟩, hρ, rfl⟩⟩
  have hQn : ∀ a ∈ A, ∀ q ∈ Q, a * q * a⁻¹ ∈ Q := by
    intro a ha q hq
    have hqA := hQA hq
    rw [hmemQ (A.mul_mem (A.mul_mem ha hqA) (A.inv_mem ha))]
    have h1 := (hmemQ hqA).mp hq
    have hρa : h.rho ⟨a, hAH ha⟩ ∈ B := ⟨⟨a, hAH ha⟩, ha, rfl⟩
    have h2 := conj_mem_map_pPrimeCore_self hρa h1
    have : h.rho ⟨a * q * a⁻¹, hAH (A.mul_mem (A.mul_mem ha hqA) (A.inv_mem ha))⟩ =
        h.rho ⟨a, hAH ha⟩ * h.rho ⟨q, hAH hqA⟩ * (h.rho ⟨a, hAH ha⟩)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [this]
    exact h2
  have h2Q : ∀ q ∈ Q, ∀ k : ℕ, q ^ 2 ^ k = 1 → q ∈ zpowers t := by
    intro q hq k hk
    have hqA := hQA hq
    have h1 := (hmemQ hqA).mp hq
    have hρ1 : h.rho ⟨q, hAH hqA⟩ = 1 := by
      obtain ⟨y, hy, hyq⟩ := h1
      have hy2 : y ^ 2 ^ k = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        simp only [Subgroup.coe_subtype] at hyq
        rw [hyq, ← map_pow]
        have : (⟨q, hAH hqA⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hk]; rfl)
        rw [this, map_one]
      have hord : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hy2
      have hdvd : orderOf y ∣ Nat.card (pPrimeCore 2 ↥B) := by
        rw [← Subgroup.orderOf_mk y hy]
        exact orderOf_dvd_natCard _
      have := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k pPrimeCore_coprime_card) hord
        hdvd
      rw [orderOf_eq_one_iff] at this
      rw [this] at hyq
      simpa using hyq.symm
    exact h.mem_zpowers_of_mem_ker (hAH hqA) ((h.mem_ker_rho _).mp hρ1) hk
  have htQ : t ∈ Q := by
    rw [hmemQ htA]
    rw [show (⟨t, hAH htA⟩ : ↥H) = ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ from rfl, h.rho_t]
    exact one_mem _
  have hQcyc : IsPGroup 2 (↥Q ⧸ pPrimeCore 2 ↥Q) := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥Q))
    refine isPGroup_quot_of_isCyclic P ?_
    have hPt : ∀ x ∈ (P : Subgroup ↥Q), (x : X) ∈ zpowers t := by
      intro x hx
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
      have hk2 : (x : X) ^ 2 ^ k = 1 := by
        have := congrArg (fun y : ↥(P : Subgroup ↥Q) => ((y : ↥Q) : X)) hk
        simpa using this
      exact h2Q x x.2 k hk2
    have hinj : Function.Injective (Q.subtype.comp (P : Subgroup ↥Q).subtype) :=
      Q.subtype_injective.comp (P : Subgroup ↥Q).subtype_injective
    have hle : (Q.subtype.comp (P : Subgroup ↥Q).subtype).range ≤ zpowers t := by
      rintro _ ⟨x, rfl⟩
      exact hPt x x.2
    have : IsCyclic ↥(Q.subtype.comp (P : Subgroup ↥Q).subtype).range :=
      Subgroup.isCyclic_of_le hle
    exact isCyclic_of_surjective
      (MonoidHom.ofInjective hinj).symm.toMonoidHom (MulEquiv.surjective _)
  rw [isPGroup_quot_iff] at hQcyc ⊢
  intro a ha
  have hρa : h.rho ⟨a, hAH ha⟩ ∈ B := ⟨⟨a, hAH ha⟩, ha, rfl⟩
  obtain ⟨k, hk⟩ := (isPGroup_quot_iff.mp hA) _ hρa
  have hak : a ^ 2 ^ k ∈ Q := by
    rw [hmemQ (A.pow_mem ha _)]
    have : h.rho ⟨a ^ 2 ^ k, hAH (A.pow_mem ha _)⟩ = h.rho ⟨a, hAH ha⟩ ^ 2 ^ k := by
      rw [← map_pow]
      rfl
    rw [this]
    exact hk
  obtain ⟨k', hk'⟩ := hQcyc _ hak
  refine ⟨k + k', ?_⟩
  rw [pow_add, pow_mul]
  refine le_map_pPrimeCore ((map_subtype_le _).trans hQA) (fun a' ha' n hn => ?_)
    (coprime_card_map_pPrimeCore _) hk'
  obtain ⟨y, hy, rfl⟩ := hn
  have hQn' := hQn a' ha'
  refine ⟨⟨a' * y * a'⁻¹, hQn' y y.2⟩, ?_, rfl⟩
  have hchar := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Q
    (pPrimeCore 2 ↥Q) (show a' ∈ normalizer (Q : Set X) from
      mem_normalizer_iff.mpr fun n => ⟨fun hn => hQn' n hn, fun hn => by
        have := hQn a'⁻¹ (A.inv_mem ha') _ hn
        simpa [mul_assoc] using this⟩)
  have h1 := (mem_normalizer_iff.mp hchar (y : X)).mp ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hy'eq⟩ := h1
  have : y' = ⟨a' * y * a'⁻¹, hQn' y y.2⟩ := Subtype.ext hy'eq
  rwa [← this]

end Standing

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem involutionInput (hI : AutPSL2InvolutionInput) (hσ : Setup42 h hS w z) :
    (∀ ι ∈ ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊓
        centralizer (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) :
          Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))), orderOf ι = 2 →
      IsPGroup 2 (↥(h.rho.range ⊓ centralizer {ι}) ⧸
        pPrimeCore 2 ↥(h.rho.range ⊓ centralizer {ι}))) ∧
    IsPGroup 2 (↥(h.rho.range ⊓ normalizer
        ((((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
          zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) : Subgroup (MulAut (Bar L))) :
          Set (MulAut (Bar L)))) ⧸
      pPrimeCore 2 ↥(h.rho.range ⊓ normalizer
        ((((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
          zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) : Subgroup (MulAut (Bar L))) :
          Set (MulAut (Bar L))))) ∧
    ∀ α ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho,
      α ∉ ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
        zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) → α ^ 2 = 1 →
        Nonempty (↥(fixedPoints α) ≃* DihedralGroup ((p ^ f + 1) / 2)) ∧
        IsPGroup 2 (↥(h.rho.range ⊓ centralizer {α}) ⧸
          pPrimeCore 2 ↥(h.rho.range ⊓ centralizer {α})) :=
  hI (Bar L) p f h.config.prime h.config.ne_two
    (h.dihedral.even p f h.config.prime h.config.ne_two h.config.lieModel) h.sixteen
    h.config.lieModel h.rho.range h.innAut_le_range _ (map_le_range _ _)
    (h.isSylowOf_rho hS).exists_sylow_eq_subgroupOf _ hσ.lift.data

theorem rho_z_mem (hσ : Setup42 h hS w z) :
    h.rho ⟨z, hS.le hσ.z_mem.1⟩ ∈ ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
        innAut (Bar L)) ⊓ centralizer (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
          innAut (Bar L) : Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))) ∧
      orderOf (h.rho ⟨z, hS.le hσ.z_mem.1⟩) = 2 := by
  have hzH : z ∈ centralizer ({t} : Set X) := hS.le hσ.z_mem.1
  refine ⟨⟨⟨⟨⟨z, hzH⟩, hσ.z_mem.1, rfl⟩,
    ⟨QuotientGroup.mk ⟨z, hσ.z_mem.2⟩, (h.rho_of_mem ⟨z, hσ.z_mem.2⟩).symm⟩⟩, ?_⟩, ?_⟩
  · rw [h.map_rho_inf_innAut hS]
    refine mem_centralizer_iff.mpr ?_
    rintro _ ⟨⟨d, hdH⟩, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hσ.z_comm_D hd)
  · have hinj := h.rhoD_injective hS
    have : orderOf ((h.rhoD hS) ⟨z, hσ.z_mem⟩) = 2 := by
      rw [orderOf_injective _ hinj, Subgroup.orderOf_mk, hσ.z_order]
    exact this

theorem isPGroup_quot_centralizer_z (hI : AutPSL2InvolutionInput) (hσ : Setup42 h hS w z) :
    IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {z}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {z})) ∧
      IsSylowOf 2 S (centralizer ({t} : Set X) ⊓ centralizer {z}) := by
  have hzH : z ∈ centralizer ({t} : Set X) := hS.le hσ.z_mem.1
  refine ⟨h.isPGroup_quot_of_rho inf_le_left ⟨mem_centralizer_singleton_iff.mpr rfl,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hzH).symm⟩ ?_,
    hS.of_le (le_inf hS.le fun s hs => mem_centralizer_singleton_iff.mpr (hσ.z_comm hs))
      inf_le_left⟩
  obtain ⟨hz, hz2⟩ := hσ.rho_z_mem
  refine isPGroup_quot_of_le ?_ ((hσ.involutionInput hI).1 _ hz hz2)
  rintro _ ⟨⟨a, haH⟩, ha, rfl⟩
  refine ⟨⟨_, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp ha.2)

theorem isPGroup_quot_centralizer_X (hI : AutPSL2InvolutionInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) :
    IsPGroup 2 (↥(centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X)) ⧸
      pPrimeCore 2 ↥(centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) :
        Set X))) ∧
      IsSylowOf 2 (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
        (centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X)) := by
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hAH : centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) ≤
      centralizer ({t} : Set X) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hg t htX).symm
  have htA : t ∈ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) :=
    mem_centralizer_iff.mpr fun x hx =>
      (mem_centralizer_iff.mp (hσ.X_le_center_T hx).2 t
        (mem_sup_left (mem_sup_left (mem_zpowers t)))).symm
  refine ⟨h.isPGroup_quot_of_rho hAH htA ?_, hσ.isSylowOf_centralizer_X hKC⟩
  obtain ⟨hz, hz2⟩ := hσ.rho_z_mem
  refine isPGroup_quot_of_le ?_ ((hσ.involutionInput hI).1 _ hz hz2)
  rintro _ ⟨⟨a, haH⟩, ha, rfl⟩
  refine ⟨⟨_, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.mp ha z hzX).symm

theorem isPGroup_quot_normalizer_T (hI : AutPSL2InvolutionInput) (hσ : Setup42 h hS w z) :
    IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓
        normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓
        normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))) ∧
      IsSylowOf 2 S (centralizer ({t} : Set X) ⊓
        normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) := by
  have htT : t ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := mem_sup_left (mem_sup_left (mem_zpowers t))
  refine ⟨h.isPGroup_quot_of_rho inf_le_left ⟨mem_centralizer_singleton_iff.mpr rfl,
    le_normalizer htT⟩ ?_, hS.of_le (le_inf hS.le hσ.S_le_normalizer_T) inf_le_left⟩
  refine isPGroup_quot_of_le ?_ (hσ.involutionInput hI).2.1
  rw [← hσ.map_rho_T]
  rintro _ ⟨⟨a, haH⟩, ha, rfl⟩
  refine ⟨⟨_, rfl⟩, show h.rho ⟨a, haH⟩ ∈ normalizer _ from ?_⟩
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨⟨b, hbH⟩, hb, rfl⟩
    refine ⟨⟨a * b * a⁻¹, mul_mem (mul_mem haH hbH) (inv_mem haH)⟩,
      (mem_normalizer_iff.mp ha.2 b).mp hb, ?_⟩
    show h.rho (⟨a, haH⟩ * ⟨b, hbH⟩ * ⟨a, haH⟩⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  · intro hy
    obtain ⟨⟨b, hbH⟩, hb, hby⟩ := hy
    refine ⟨⟨a⁻¹ * b * a, mul_mem (mul_mem (inv_mem haH) hbH) haH⟩, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem ha.2) b).mp hb
      rw [inv_inv] at this
      exact this
    · show h.rho (⟨a, haH⟩⁻¹ * ⟨b, hbH⟩ * ⟨a, haH⟩) = y
      rw [map_mul, map_mul, map_inv, hby]
      group

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
