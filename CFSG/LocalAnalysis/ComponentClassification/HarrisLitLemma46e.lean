module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitDihedralSwap

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

theorem two_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (h : H < K) :
    2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨c, hc⟩ := card_dvd_of_le h.le
  have hlt := card_lt_of_lt h
  rw [hc] at hlt ⊢
  have h2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hlt
    · simp at hlt
    · omega
  calc 2 * Nat.card H ≤ c * Nat.card H := Nat.mul_le_mul_right _ h2
    _ = Nat.card H * c := mul_comm _ _

theorem card_le_four_of_cyclic_index_two {G : Type*} [Group G] [Finite G] {Z : Subgroup G}
    (hZ : IsCyclic Z) (hind : Z.index ≤ 2) {E : Subgroup G} (hE : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card E ≤ 4 := by
  have hpos : Z.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hZn : Z.Normal := by
    rcases (show Z.index = 1 ∨ Z.index = 2 by omega) with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  have h1 : Nat.card (Z.subgroupOf E) ≤ 2 := by
    let φ : Z.subgroupOf E →* Z :=
      { toFun := fun x => ⟨(x : E), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := fun x y hxy => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Z => (z : G)) hxy
    have : IsCyclic (Z.subgroupOf E) := isCyclic_of_injective φ hφ
    have hexp : Monoid.exponent (Z.subgroupOf E) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        apply Subtype.ext
        apply Subtype.ext
        simpa using hE ((x : E) : G) (x : E).2
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  have h2 : (Z.subgroupOf E).index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos)
      (relIndex_dvd_index_of_normal (H := Z) (K := E))).trans hind
  calc Nat.card E = Nat.card (Z.subgroupOf E) * (Z.subgroupOf E).index :=
        (Subgroup.card_mul_index (Z.subgroupOf E)).symm
    _ ≤ 2 * 2 := Nat.mul_le_mul h1 h2

theorem card_le_four_of_mulEquiv {G Y : Type*} [Group G] [Finite G] [Group Y] {R E : Subgroup G}
    (e : ↥R ≃* Y) {Z : Subgroup Y} (hZ : IsCyclic Z) (hind : Z.index ≤ 2) (hER : E ≤ R)
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 4 := by
  have : Finite Y := Finite.of_equiv _ e.toEquiv
  have hcard : Nat.card ((E.subgroupOf R).map e.toMonoidHom) = Nat.card E := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hER).toEquiv
  rw [← hcard]
  refine card_le_four_of_cyclic_index_two hZ hind ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, ← map_pow]
  have : x ^ 2 = 1 := Subtype.ext (by simpa using hE _ hx)
  rw [this, map_one]

theorem index_zpowers_r_one {n : ℕ} [NeZero n] :
    (zpowers (DihedralGroup.r 1 : DihedralGroup n)).index = 2 := by
  have h1 := (zpowers (DihedralGroup.r 1 : DihedralGroup n)).card_mul_index
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h1
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  exact Nat.eq_of_mul_eq_mul_left hn (by rw [h1, mul_comm])

theorem card_le_four_of_sylow_shape {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (hC : ∀ R : Subgroup G, IsSylowOf 2 R C →
      Nat.card R = 4 ∨ (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥R ≃* DihedralGroup (2 ^ k))) ∨
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥R ≃* CFSG.Open.SemidihedralGroup n))
    {E : Subgroup G} (hEC : E ≤ C) (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE _ x.2)⟩
  obtain ⟨R, hR, hER⟩ := exists_isSylowOf_ge hE2 hEC
  rcases hC R hR with h4 | ⟨k, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rw [← h4]
    exact card_le_of_le hER
  · have : NeZero (2 ^ k) := ⟨by positivity⟩
    exact card_le_four_of_mulEquiv e inferInstance index_zpowers_r_one.le hER hE
  · exact card_le_four_of_mulEquiv e (CFSG.Semidihedral.rotationSubgroup_cyclic n)
      (CFSG.Semidihedral.rotationSubgroup_index n (by omega)).le hER hE

open DihedralGroup in
theorem dihedral_centralizer_sr_zero {m : ℕ} (hm : 1 ≤ m) :
    (∀ x ∈ centralizer ({sr 0} : Set (DihedralGroup (2 ^ m))), x ^ 2 = 1) ∧
      4 ≤ Nat.card (centralizer ({sr 0} : Set (DihedralGroup (2 ^ m)))) := by
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a : DihedralGroup (2 ^ m) := r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) with ha
  have hmem : ∀ x : DihedralGroup (2 ^ m),
      x ∈ centralizer ({sr 0} : Set (DihedralGroup (2 ^ m))) ↔
        x = 1 ∨ x = a ∨ x = sr 0 ∨ x = sr (0 + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := fun x => by
    rw [mem_centralizer_singleton_iff]
    exact dihedral_commute_sr_iff hm x 0
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [dihedral_sq_eq_one_iff hm]
    rcases (hmem x).mp hx with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨0, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
  · have ha1 : a ≠ 1 := by
      rw [ha, one_def, Ne, r.injEq, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have h1 := Nat.le_of_dvd (by positivity) hdvd
      have h2 := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (show m - 1 < m by omega)
      omega
    have ha2 : a ^ 2 = 1 := (dihedral_sq_eq_one_iff hm a).mpr (Or.inr (Or.inl rfl))
    have hao : orderOf a = 2 := orderOf_eq_prime ha2 ha1
    have haC := (hmem a).mpr (Or.inr (Or.inl rfl))
    have hbC := (hmem (sr 0)).mpr (Or.inr (Or.inr (Or.inl rfl)))
    have hbZ : (sr 0 : DihedralGroup (2 ^ m)) ∉ zpowers a := by
      intro hb
      rcases eq_one_or_eq_of_mem_zpowers hao hb with h1 | h1
      · rw [one_def] at h1
        cases h1
      · rw [ha] at h1
        cases h1
    have h2 := two_mul_card_le_of_lt
      (IsConcreteLE.lt_iff_le_and_exists.mpr ⟨zpowers_le.mpr haC, sr 0, hbC, hbZ⟩)
    rwa [Nat.card_zpowers, hao] at h2

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem beta_not_mem_L (hσ : Setup42 h hS w z) (i j : ℕ) :
    w ^ (orderOf w / 2) * t ^ i * z ^ j ∉ L := fun hβL =>
  hσ.rho_beta_not_mem_inn i j ⟨QuotientGroup.mk ⟨_, hβL⟩, (h.rho_of_mem ⟨_, hβL⟩).symm⟩

theorem commutator_KBar_conj_ne_bot (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    ∀ g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      ⁅KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
        (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set K := centralizerResidual L β with hK
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  intro g hcomm
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at hcomm
  obtain ⟨m, hm, ⟨e⟩⟩ := hσ.dihedral_Dstar hFC hKC i j
  have hDM : S ⊓ L ⊓ K ≤ M := fun x hx => (centralizerResidual_le hx.2).2
  set U : Subgroup ↥M := (S ⊓ M).subgroupOf M with hU
  have hU2 : IsPGroup 2 U := (hS.isPGroup.to_le inf_le_left).comap_subtype
  have hinjU : Set.InjOn π U := GSThmB.OddQuot.injOn_of_isPGroup hU2
  have hDU : ∀ x : ↥(S ⊓ L ⊓ K), (⟨(x : X), hDM x.2⟩ : ↥M) ∈ U := fun x => ⟨x.2.1.1, hDM x.2⟩
  have hβU : (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥M) ∈ U :=
    ⟨hσ.beta_mem_S i j, mem_centralizer_singleton_iff.mpr rfl⟩
  set φ : DihedralGroup (2 ^ m) →* MBar β := (MulAut.conj g).toMonoidHom.comp
    (π.comp ((Subgroup.inclusion hDM).comp e.symm.toMonoidHom)) with hφ
  have hφ_apply : ∀ x, φ x = g * π ⟨(e.symm x : X), hDM (e.symm x).2⟩ * g⁻¹ := fun _ => rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    rw [hφ_apply, hφ_apply, mul_left_inj, mul_right_inj] at hxy
    have h1 : (e.symm x : X) = (e.symm y : X) :=
      congrArg (fun y : ↥M => (y : X)) (hinjU (hDU (e.symm x)) (hDU (e.symm y)) hxy)
    exact e.symm.injective (Subtype.ext h1)
  obtain ⟨hVexp, hVcard⟩ := dihedral_centralizer_sr_zero (m := m) (by omega)
  set V := (centralizer ({DihedralGroup.sr 0} : Set (DihedralGroup (2 ^ m)))).map φ with hV
  have hVexp' : ∀ x ∈ V, x ^ 2 = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_pow, hVexp v hv, map_one]
  have hVcard' : Nat.card V =
      Nat.card (centralizer ({DihedralGroup.sr 0} : Set (DihedralGroup (2 ^ m)))) :=
    card_map_of_injective hφinj
  have hVK : V ≤ centralizer (KBar L β : Set (MBar β)) := by
    rintro _ ⟨v, -, rfl⟩
    exact hcomm ⟨π ⟨(e.symm v : X), hDM (e.symm v).2⟩,
      ⟨⟨(e.symm v : X), hDM (e.symm v).2⟩, (e.symm v).2.2, rfl⟩, rfl⟩
  have hβV : betaBar β ∉ V := by
    rintro ⟨v, -, hv⟩
    rw [hφ_apply] at hv
    have hc := mem_center_iff.mp (betaBar_mem_center β) g
    have h1 : π ⟨(e.symm v : X), hDM (e.symm v).2⟩ = betaBar β :=
      calc π ⟨(e.symm v : X), hDM (e.symm v).2⟩ =
            g⁻¹ * (g * π ⟨(e.symm v : X), hDM (e.symm v).2⟩ * g⁻¹) * g := by group
        _ = g⁻¹ * betaBar β * g := by rw [hv]
        _ = betaBar β := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    have h2 : (e.symm v : X) = β := congrArg Subtype.val (hinjU (hDU (e.symm v)) hβU h1)
    apply hσ.beta_not_mem_L i j
    show β ∈ L
    rw [← h2]
    exact (e.symm v).2.1.2
  have : (zpowers (betaBar β)).Normal :=
    normal_of_le_center (zpowers_le.mpr (betaBar_mem_center β))
  have hb2 : betaBar β ^ 2 = 1 := by
    rw [betaBar, ← QuotientGroup.mk_pow]
    rw [show (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({β} : Set X))) ^ 2 =
      1 from Subtype.ext (by rw [Subgroup.coe_pow, hσ.sq_eq_one_of_mem_X (beta_mem_X i j),
        Subgroup.coe_one]), QuotientGroup.mk_one]
  have hEexp : ∀ x ∈ V ⊔ zpowers (betaBar β), x ^ 2 = 1 := by
    intro x hx
    obtain ⟨y, hy, c, hc, rfl⟩ := mem_sup_of_normal_right.mp hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    have hyc : Commute y (betaBar β ^ k) :=
      Commute.zpow_right (mem_center_iff.mp (betaBar_mem_center β) y) k
    rw [hyc.mul_pow, hVexp' y hy, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hb2, one_zpow]
  have hEK : V ⊔ zpowers (betaBar β) ≤ centralizer (KBar L β : Set (MBar β)) :=
    sup_le hVK (zpowers_le.mpr (betaBar_mem_centralizer_K β))
  have h8 : 2 * Nat.card V ≤ Nat.card ↥(V ⊔ zpowers (betaBar β)) :=
    two_mul_card_le_of_lt (IsConcreteLE.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, betaBar β, mem_sup_right (mem_zpowers _), hβV⟩)
  have h4 : Nat.card ↥(V ⊔ zpowers (betaBar β)) ≤ 4 :=
    card_le_four_of_sylow_shape (hσ.lemma46b hFC hKC i j).2 hEK hEexp
  omega

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
