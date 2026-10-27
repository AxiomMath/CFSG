module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PL
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Setup

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem odd_orderOf_of_central {J Y : Type*} [Group J] [Finite J] [Group Y] [IsSimpleGroup Y]
    (hY : ∃ a b : Y, a * b ≠ b * a) (e : J ⧸ pPrimeCore 2 J ≃* Y) {c : J}
    (hc : ∀ k : J, c * k = k * c) : Odd (orderOf c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : e (QuotientGroup.mk c) ∈ center Y := by
    rw [mem_center_iff]
    intro y
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc k]
  rw [LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hY, mem_bot,
    MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hcen
  have hdvd : orderOf c ∣ Nat.card (pPrimeCore 2 J) := Subgroup.orderOf_dvd_natCard _ hcen
  have hodd : Odd (Nat.card (pPrimeCore 2 J)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact hodd.of_dvd_nat hdvd

theorem mem_normalizer_of_map_eq {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    have : y = x := by
      have := congrArg (fun u => g⁻¹ * u * g) hyx'
      simpa [mul_assoc] using this
    rwa [← this]

end L415

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem z₂_mem_F : t * z₁ * t⁻¹ ∈ centralizer ({z₁} : Set X) :=
  mem_centralizer_singleton_iff.mpr (hD.comm_z₂ hD.z₁_mem_V₀).symm

theorem nonempty_K₂F_equiv :
    Nonempty (↥(barOf (centralizer {z₁}) K₂) ⧸ pPrimeCore 2 ↥(barOf (centralizer {z₁}) K₂) ≃*
      ↥(Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  obtain ⟨-, -, ⟨e⟩⟩ := L415.isPComponent_barOf hD.beta_mem_F hD.orderOf_beta
    hD.fd.isTwoComponentIn_K₂
  obtain ⟨e'⟩ := hD.fd.bar_K₂
  exact ⟨e.symm.trans e'⟩

theorem odd_of_central {c : MBar z₁} (hc : c ∈ barOf (centralizer {z₁}) K₂)
    (hcc : ∀ k ∈ barOf (centralizer {z₁}) K₂, c * k = k * c) : Odd (orderOf c) := by
  obtain ⟨e⟩ := hD.nonempty_K₂F_equiv
  obtain ⟨hs, hnab⟩ := L415.simple_nonabelian_of_lieModel (hD.hs.lieModel_KBar hD.h412)
  have := hs
  have h := L415.odd_orderOf_of_central hnab e (c := ⟨c, hc⟩) (fun k => Subtype.ext (hcc k k.2))
  rwa [Subgroup.orderOf_mk] at h

theorem orderOf_z₂F :
    orderOf (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({z₁} : Set X)))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  refine orderOf_mk_eq_two hodd ?_
  rw [Subgroup.orderOf_mk]
  refine orderOf_eq_prime ?_ hD.z₂_ne_one
  rw [sq, show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ * z₁) * t⁻¹ by group, hD.z₁_mul_z₁]
  group

theorem z₂F_mem : (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) ∈
    barOf (centralizer {z₁}) K₂ :=
  mk_mem_barOf hD.z₂_mem_F hD.fd.z₂_mem

theorem exists_not_comm_z₂F : ∃ k ∈ barOf (centralizer {z₁}) K₂,
    k * (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) ≠
      (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) * k := by
  by_contra h
  push Not at h
  have h1 := hD.odd_of_central hD.z₂F_mem (fun k hk => (h k hk).symm)
  rw [hD.orderOf_z₂F] at h1
  exact (Nat.not_odd_iff_even.mpr even_two) h1

theorem z₂F_comm_betaF : (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) *
    QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ =
    QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ *
      QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hD.z₂_comm_beta

theorem betaF_mul_betaF :
    (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁) *
      QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ = 1 := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_one]
  congr 1
  exact Subtype.ext hD.beta_mul_beta

theorem isSylowOf_V₀F : IsSylowOf 2 (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁})) ⊤ :=
  isSylowOf_barOf hD.fd.isSylowOf_𝒱₀

theorem V₀F_comm_z₂F {v : MBar z₁} (hv : v ∈ barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁})) :
    v * QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ =
      QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ * v := by
  obtain ⟨x, hx, rfl⟩ := hv
  change QuotientGroup.mk x * _ = _ * QuotientGroup.mk x
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hD.comm_z₂ hx)

omit [Finite X] hD in
theorem W₀F_le_V₀F : barOf (centralizer {z₁})
    (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ≤
    barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, (mem_inf.mp hx).1, rfl⟩

theorem W₀F_le_centralizer : barOf (centralizer {z₁})
    (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ≤
    centralizer {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ :
      MBar z₁)} := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_singleton_iff]
  change QuotientGroup.mk x * _ = _ * QuotientGroup.mk x
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2)

theorem relIndex_W₀F_le : (barOf (centralizer {z₁})
    (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).relIndex
    (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁})) ≤ 4 := by
  have hp : IsPGroup 2 ↥(𝒱 ⊓ centralizer ({z₁} : Set X)) :=
    hD.fd.isSylowOf_𝒱.isPGroup.to_le inf_le_left
  have h1 := Subgroup.relIndex_mul_card (barOf (centralizer {z₁})
    (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}))
    (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}))
  rw [inf_of_le_left W₀F_le_V₀F, card_barOf inf_le_right hp,
    card_barOf (inf_le_left.trans inf_le_right) (hp.to_le inf_le_left)] at h1
  have h2 := hD.fd.card_𝒱₀_le
  have hpos : 0 < Nat.card ↥(𝒱 ⊓ centralizer {z₁} ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) := Nat.card_pos
  by_contra h3
  push Not at h3
  have h4 : 5 * Nat.card ↥(𝒱 ⊓ centralizer {z₁} ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ≤ _ := Nat.mul_le_mul_right _ h3
  omega

theorem exists_sylow_K₂F : ∃ Q : Subgroup (MBar z₁), Q ≤ barOf (centralizer {z₁}) K₂ ∧
    IsPGroup 2 Q ∧ 8 ≤ Nat.card Q ∧
    ∀ q ∈ Q, (∀ k ∈ barOf (centralizer {z₁}) K₂, q * k = k * q) → q = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, -⟩ := exists_isSylowOf_ge (IsPGroup.of_bot (p := 2))
    (bot_le : (⊥ : Subgroup (MBar z₁)) ≤ barOf (centralizer {z₁}) K₂)
  refine ⟨Q, hQ.le, hQ.isPGroup, ?_, ?_⟩
  · obtain ⟨m, hm, ⟨eD⟩⟩ := hD.hs.setup.dihedral
    obtain ⟨e⟩ := hD.nonempty_K₂F_equiv
    have h1 := HarrisEnd.factorization_two_card_quotient (pPrimeCore 2
      ↥(barOf (centralizer {z₁}) K₂)) (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    rw [Nat.card_congr e.toEquiv, hD.hs.factorization_card_KBar hD.h412 eD] at h1
    rw [hQ.card_eq, h1]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · intro q hq hqc
    have h1 := hD.odd_of_central (hQ.le hq) hqc
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ.isPGroup) ⟨q, hq⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk] at h1
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exfalso
      rw [pow_succ] at h1
      exact (Nat.not_odd_iff_even.mpr (Even.mul_left even_two _)) h1

theorem exists_component [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) :
    ∃ M : Subgroup (MBar z₁), IsComponent M ∧
      conjugate M (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩) = M ∧
      barOf (centralizer {z₁}) K₂ ≤ M ∧
      IsPComponent 2 ((barOf (centralizer {z₁}) K₂).subgroupOf (M ⊓ centralizer
        {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁)})) ∧
      (∀ v : MBar z₁, v * QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ =
        QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ * v →
          M.map (MulAut.conj v).toMonoidHom = M) ∧
      IsSylowOf 2 (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M) M ∧
      Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M) ≤
        (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁} ⊓
          centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).relIndex
          (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁})) *
        Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M ⊓
          centralizer {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
            hD.beta_mem_F⟩ : MBar z₁)}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hM, hKI, hKpc⟩ := hD.exists_orbit_component hnab hK hSch
  have hO : pPrimeCore 2 (MBar z₁) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hMc : IsComponent M :=
    (isTwoComponent_iff_isComponent hO M).mp ((isTwoComponent_iff_isPComponent M).mpr hM)
  obtain ⟨hKb, -, -⟩ := L415.isPComponent_barOf hD.beta_mem_F hD.orderOf_beta
    hD.fd.isTwoComponentIn_K₂
  have hinv := fun v hv => L415.map_conj_sup_eq hMc hD.betaF_mul_betaF hD.z₂F_comm_betaF hKI
    hD.z₂F_mem hD.exists_not_comm_z₂F (v := v) hv
  have hVN : barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ≤
      normalizer ((M ⊔ conjugate M (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
        hD.beta_mem_F⟩) : Subgroup (MBar z₁)) : Set (MBar z₁)) := fun v hv =>
    L415.mem_normalizer_of_map_eq (hinv v (hD.V₀F_comm_z₂F hv))
  have hM'E : conjugate M (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
      hD.beta_mem_F⟩) ≤ layer (MBar z₁) :=
    LocalCores.component_le_layer (LocalCores.isComponent_map_mulEquiv _ hMc)
  have hIN : M ⊔ conjugate M (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
      hD.beta_mem_F⟩) ≤ normalizer (M : Set (MBar z₁)) :=
    (sup_le (LocalCores.component_le_layer hMc) hM'E).trans (LocalCores.layer_le_normalizer hMc)
  have hPsyl := L415.isSylowOf_inf_inf hD.isSylowOf_V₀F hVN le_sup_left hIN
  have hPle := L415.card_le_relIndex_mul (W := barOf (centralizer {z₁})
    (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}))
    (inf_le_left.trans inf_le_left : barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓
      (M ⊔ conjugate M (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
        hD.beta_mem_F⟩)) ⊓ M ≤ barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}))
  have heq : M = conjugate M (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
      hD.beta_mem_F⟩) := by
    by_contra hne
    obtain ⟨Q, hQK, hQ2, hQ8, hQZ⟩ := hD.exists_sylow_K₂F
    refine L415.false_of_swap hMc hne hKI hKb hQK hQ2 hQ8 hQZ hPsyl ?_
    refine hPle.trans ?_
    calc _ ≤ 4 * Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓
          (M ⊔ conjugate M (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
            hD.beta_mem_F⟩)) ⊓ M ⊓ barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁} ⊓
              centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) :=
          Nat.mul_le_mul_right _ hD.relIndex_W₀F_le
      _ ≤ _ := Nat.mul_le_mul_left _ (Subgroup.card_le_of_le
          (inf_le_inf_left _ hD.W₀F_le_centralizer))
  have hsup : M ⊔ conjugate M (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
      hD.beta_mem_F⟩) = M := by rw [← heq, sup_idem]
  have hVM : barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M ⊓ M =
      barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M := by rw [inf_assoc, inf_idem]
  rw [hsup] at hKI hKpc hinv hPsyl hPle
  rw [hVM] at hPsyl hPle
  refine ⟨M, hMc, heq.symm, hKI, hKpc, hinv, hPsyl, hPle.trans ?_⟩
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (inf_le_inf_left _ hD.W₀F_le_centralizer))

end Data415B

end CFSG.ComponentClassification.HarrisLit
