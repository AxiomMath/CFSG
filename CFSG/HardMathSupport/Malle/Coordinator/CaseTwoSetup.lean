module

public import CFSG.HardMathSupport.Malle.Coordinator.CaseTwoCore
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4Structure
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4CaseTwoInputs

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

open CFSG.AGLEmbedding CFSG.Quasithin

variable {Y : Type} [Group Y]

theorem card_map_conj (F : Subgroup Y) (c : Y) :
    Nat.card (F.map (MulAut.conj c).toMonoidHom) = Nat.card F :=
  Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem exists_caseTwo_data [Finite Y]
    (hSig : ReeF4OuterSigmaFixedOrder)
    (K : Subgroup Y) [K.Normal] (d : TauCeti.ValidLieTypeIndex) (hd : IsReeFFourFiveIndex d)
    (e : Nonempty (K ≃* CatGroup d)) (hCK : Subgroup.centralizer (K : Set Y) = ⊥)
    (T : Sylow 5 Y) (h3 : 3 ≤ CFSG.Open.pRank 5 (T : Subgroup Y)) :
    Nat.card K = reeF4Order ∧ K.index = 5 ∧
    Nat.card ((T : Subgroup Y) ⊓ K : Subgroup Y) = 625 ∧
    IsPGroup 5 ((T : Subgroup Y) ⊓ K : Subgroup Y) ∧
    Nat.card (centerOf (T : Subgroup Y)) = 25 ∧
    K ⊓ Subgroup.centralizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) ≤
      (T : Subgroup Y) ⊓ K ∧
    (∃ i j h t : Y, CFSG.Quasithin.B45Tor.IsGL23Data (centerOf (T : Subgroup Y)) i j h t) ∧
    ∃ φ : Y, φ ∈ (T : Subgroup Y) ∧
      OuterFiveData ((T : Subgroup Y) ⊓ K) (centerOf (T : Subgroup Y)) φ ∧
      ∀ F : Subgroup Y, F ≤ K → F ≤ Subgroup.centralizer ({φ} : Set Y) →
        Nat.card F ∣ 35942400 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set P := (T : Subgroup Y) ⊓ K with hP
  set Z := centerOf (T : Subgroup Y) with hZdef
  obtain ⟨hZK, hZe, hZc, hCZT, hGL⟩ := LocalAction.reeF4_core_of_certs K d hd e hCK T h3
  have hKcard : Nat.card K = reeF4Order := by
    obtain ⟨F, _, _, _, hF, ⟨eΓ⟩⟩ := LocalAction.exists_reeGamma_model hd e
    rw [Nat.card_congr eΓ.toEquiv, LocalAction.card_reeGamma_thirtyTwo hF]
  have hrankY : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y) :=
    h3.trans (LocalAction.pRank_mono_of_le' (by norm_num) le_top)
  have hidx5 : K.index = 5 := (LocalAction.exists_outer_sigma K d hd e hCK hrankY).1
  have hP5 : IsPGroup 5 P := T.isPGroup'.to_inf_left
  have hPidx : ¬ 5 ∣ P.relIndex K := OvergroupTransport.not_dvd_relIndex_inf_sylow K T
  have hshape := LocalAction.sylowShape_five_of_catGroup hd e
  obtain ⟨ePK⟩ := hshape (P.subgroupOf K) hP5.comap_subtype hPidx
  let eP : P ≃* LocalAction.V5 :=
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ≤ K)).symm.trans ePK
  have hPcard : Nat.card P = 625 := by
    rw [Nat.card_congr eP.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    have h := congrArg Subtype.val (eP.injective (show eP (⟨a, ha⟩ * ⟨b, hb⟩) =
      eP (⟨b, hb⟩ * ⟨a, ha⟩) by rw [map_mul, map_mul, mul_comm]))
    simpa using h
  have hPexp : ∀ y ∈ P, y ^ 25 = 1 := by
    intro y hy
    have h1 : eP (⟨y, hy⟩ ^ 25) = 1 := by
      rw [map_pow]
      funext k
      simp only [Pi.pow_apply, Pi.one_apply]
      rw [← ofAdd_toAdd (eP ⟨y, hy⟩ k), ← ofAdd_nsmul]
      show Multiplicative.ofAdd ((25 : ℕ) • Multiplicative.toAdd (eP ⟨y, hy⟩ k)) = 1
      have : ((25 : ℕ) • Multiplicative.toAdd (eP ⟨y, hy⟩ k) : ZMod (5 ^ 2)) = 0 := by
        rw [nsmul_eq_mul]
        have : ((25 : ℕ) : ZMod (5 ^ 2)) = 0 := by decide
        rw [this, zero_mul]
      rw [this]; rfl
    have h2 : (⟨y, hy⟩ : P) ^ 25 = 1 := eP.injective (by rw [h1, map_one])
    simpa using congrArg Subtype.val h2
  have hZP : Z ≤ P := le_inf (inf_le_left) hZK
  have hΩ : ∀ y ∈ P, y ^ 5 = 1 → y ∈ Z := by
    intro y hy hy5
    let Ω : Subgroup P :=
      (powMonoidHom 5 : LocalAction.V5 →* LocalAction.V5).ker.comap eP.toMonoidHom
    have hmemΩ : ∀ x : P, x ∈ Ω ↔ x ^ 5 = 1 := by
      intro x
      simp only [Ω, Subgroup.mem_comap, MonoidHom.mem_ker, powMonoidHom_apply,
        MulEquiv.coe_toMonoidHom]
      constructor
      · intro h; apply eP.injective; rw [map_pow, h, map_one]
      · intro h; rw [← map_pow, h, map_one]
    have hΩcard : Nat.card Ω = 25 := by
      have : Ω.map eP.toMonoidHom = (powMonoidHom 5 : LocalAction.V5 →* LocalAction.V5).ker :=
        Subgroup.map_comap_eq_self_of_surjective eP.surjective _
      rw [← Subgroup.card_map_of_injective (f := eP.toMonoidHom) eP.injective, this,
        LocalAction.card_ker5]
    have hZΩ : Z.subgroupOf P ≤ Ω := by
      intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      rw [hmemΩ]
      exact Subtype.ext (by simpa using hZe.2 _ hz)
    have hZcard' : Nat.card (Z.subgroupOf P) = 25 := by
      rw [card_subgroupOf_of_le hZP, hZc]; rfl
    have heq : Z.subgroupOf P = Ω :=
      Subgroup.eq_of_le_of_card_ge hZΩ (by rw [hΩcard, hZcard'])
    have hyΩ : (⟨y, hy⟩ : P) ∈ Ω := by
      rw [hmemΩ]
      exact Subtype.ext (by simpa using hy5)
    rw [← heq, Subgroup.mem_subgroupOf] at hyΩ
    exact hyΩ
  have hCZ : K ⊓ Subgroup.centralizer (Z : Set Y) ≤ P := by
    rw [hCZT]
    intro x hx
    exact ⟨hx.2, hx.1⟩
  obtain ⟨σ, hσK, hσo, hσ25, hσfix⟩ := hSig Y K d hd inferInstance e hCK hrankY
  have hσp : IsPGroup 5 (Subgroup.zpowers σ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσo, pow_one])
  obtain ⟨Q, hQ⟩ := hσp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y Q T
  set φ := c * σ * c⁻¹ with hφ
  have hφT : φ ∈ (T : Subgroup Y) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨σ, hQ (Subgroup.mem_zpowers σ), by simp [MulAut.smul_def, MulAut.conj_apply, hφ]⟩
  have hφo : orderOf φ = 5 := by
    rw [← hσo, ← MulEquiv.orderOf_eq (MulAut.conj c) σ]
    rfl
  have htransfer : ∀ F : Subgroup Y, F ≤ K → F ≤ Subgroup.centralizer ({φ} : Set Y) →
      F.map (MulAut.conj c⁻¹).toMonoidHom ≤ K ∧
        F.map (MulAut.conj c⁻¹).toMonoidHom ≤ Subgroup.centralizer ({σ} : Set Y) := by
    intro F hFK hFφ
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.Normal.conj_mem inferInstance x (hFK hx) c⁻¹
    · rintro _ ⟨x, hx, rfl⟩
      have hxφ := Subgroup.mem_centralizer_singleton_iff.mp (hFφ hx)
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc c⁻¹ * x * c * σ = c⁻¹ * (x * (c * σ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * σ * c⁻¹) * x) * c := by rw [← hφ, hxφ]
        _ = σ * (c⁻¹ * x * c) := by group
  have hφfix : ∀ F : Subgroup Y, F ≤ K → F ≤ Subgroup.centralizer ({φ} : Set Y) →
      Nat.card F ∣ 35942400 := by
    intro F hFK hFφ
    obtain ⟨h1, h2⟩ := htransfer F hFK hFφ
    rw [← card_map_conj F c⁻¹]
    exact hσfix _ h1 h2
  have hφ25 : ∀ F : Subgroup Y, IsPGroup 5 F → F ≤ K →
      F ≤ Subgroup.centralizer ({φ} : Set Y) → Nat.card F ≤ 25 := by
    intro F hF5 hFK hFφ
    obtain ⟨h1, h2⟩ := htransfer F hFK hFφ
    rw [← card_map_conj F c⁻¹]
    exact hσ25 _ (hF5.map _) h1 h2
  have hφZ : ∀ z ∈ Z, φ * z = z * φ := by
    intro z hz
    exact Subgroup.mem_centralizer_iff.mp hz.2 φ hφT
  have hφ5 : φ ^ 5 = 1 := by rw [← hφo]; exact pow_orderOf_eq_one φ
  have D : OuterFiveData P Z φ := by
    refine ⟨hPab, hPexp, hZP, hΩ, hZe.2, ?_, ?_, hφZ, ?_, hφ5⟩
    · intro y hy
      refine ⟨?_, ?_⟩
      · exact T.1.mul_mem (T.1.mul_mem (T.1.inv_mem hφT) hy.1) hφT
      · simpa using Subgroup.Normal.conj_mem inferInstance y hy.2 φ⁻¹
    · intro y hy
      refine ⟨?_, ?_⟩
      · exact T.1.mul_mem (T.1.mul_mem hφT hy.1) (T.1.inv_mem hφT)
      · exact Subgroup.Normal.conj_mem inferInstance y hy.2 φ
    · intro y hy hyφ
      set CP := P ⊓ Subgroup.centralizer ({φ} : Set Y) with hCP
      have hCP25 : Nat.card CP ≤ 25 :=
        hφ25 CP (hP5.to_le inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right
      have hZCP : Z ≤ CP := le_inf hZP (fun z hz =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hφZ z hz).symm)
      have heq : Z = CP := Subgroup.eq_of_le_of_card_ge hZCP (by rw [hZc]; exact hCP25)
      rw [heq]
      exact ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyφ.symm⟩
  exact ⟨hKcard, hidx5, hPcard, hP5, by rw [hZc]; rfl, hCZ, hGL, φ, hφT, D, hφfix⟩

theorem exists_pow_mem_conj_eq [Finite Y] {K Z : Subgroup Y} [K.Normal] (hKidx : K.index = 5)
    {i : Y} (hi4 : ∀ z ∈ Z, i ^ 4 * z * (i ^ 4)⁻¹ = z) :
    ∃ i₀ ∈ Subgroup.zpowers i, i₀ ∈ K ∧ ∀ z ∈ Z, i₀ * z * i₀⁻¹ = i * z * i⁻¹ := by
  set o := orderOf i with ho
  have ho0 : o ≠ 0 := (orderOf_pos i).ne'
  set k := o.factorization 5
  set b := o / 5 ^ k with hb
  have hbo : 5 ^ k * b = o := Nat.ordProj_mul_ordCompl_eq_self o 5
  have hbcop : Nat.Coprime 5 b := Nat.coprime_ordCompl Nat.prime_five ho0
  refine ⟨i ^ (5 ^ k), Subgroup.npow_mem_zpowers i _, ?_, ?_⟩
  ·
    have h1 : (i ^ (5 ^ k)) ^ b ∈ K := by
      rw [← pow_mul, hbo, ho, pow_orderOf_eq_one]; exact K.one_mem
    have h2 : (i ^ (5 ^ k)) ^ 5 ∈ K := by
      have := K.pow_index_mem (i ^ (5 ^ k))
      rwa [hKidx] at this
    exact mem_of_pow_mem_of_coprime hbcop h2 h1
  ·
    intro z hz
    have hmod : 5 ^ k % 4 = 1 := by
      rw [Nat.pow_mod]; norm_num
    obtain ⟨m, hm⟩ : ∃ m, 5 ^ k = 4 * m + 1 := ⟨5 ^ k / 4, by omega⟩
    have hpow : ∀ n : ℕ, (i ^ 4) ^ n * z * ((i ^ 4) ^ n)⁻¹ = z := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (i ^ 4) ^ (n + 1) * z * ((i ^ 4) ^ (n + 1))⁻¹
            = (i ^ 4) ^ n * (i ^ 4 * z * (i ^ 4)⁻¹) * ((i ^ 4) ^ n)⁻¹ := by group
          _ = z := by rw [hi4 z hz, ih]
    calc i ^ (5 ^ k) * z * (i ^ (5 ^ k))⁻¹ = i * ((i ^ 4) ^ m * z * ((i ^ 4) ^ m)⁻¹) * i⁻¹ := by
          rw [hm, pow_succ, pow_mul]; group
      _ = i * z * i⁻¹ := by rw [hpow m]

end CFSG.HardMathSupport.Malle.Coordinator
