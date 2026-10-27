module

public import CFSG.GH74.GLS.Stage2.Final.ClassicalLib
public import CFSG.GH74.GLS.Stage2.Final.ClassicalLayerN
public import CFSG.GH74.GLS.Stage2.Final.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Main
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec7

theorem exists_prime_pow_of_field (F : Type) [Field F] [Finite F] :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ Nat.card F = p ^ f := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  exact ⟨ringChar F, n, hp, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn⟩

theorem exists_model_psp (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (h3 : 3 < p ^ f) :
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs), LieModel Gs .PSp 2 p f := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨StatedProj (StatedSp 2 (GaloisField p f)), inferInstance, inferInstance,
    Or.inl ⟨by decide, ?_⟩⟩
  refine ⟨⟨hp, hf, le_refl _, ?_⟩, GaloisField p f, inferInstance, inferInstance,
    GaloisField.card p f (by omega), ⟨MulEquiv.refl _⟩⟩
  intro h
  have := congrArg Prod.snd h
  simp at this
  omega

theorem exists_model_psl (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) :
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs), LieModel Gs .PSL 4 p f := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨StatedProj (StatedSL 4 (GaloisField p f)), inferInstance, inferInstance,
    Or.inl ⟨by decide, ?_⟩⟩
  refine ⟨⟨hp, hf, by norm_num, ?_, ?_⟩, GaloisField p f, inferInstance, inferInstance,
    GaloisField.card p f (by omega), ⟨MulEquiv.refl _⟩⟩
  · intro h; have := congrArg Prod.fst h; simp at this
  · intro h; have := congrArg Prod.fst h; simp at this

theorem exists_model_psu (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) :
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs), LieModel Gs .PSU 4 p f := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨StatedProj (StatedSU 4 (p ^ f) (GaloisField p (2 * f))), inferInstance, inferInstance,
    Or.inl ⟨by decide, ?_⟩⟩
  refine ⟨⟨hp, hf, by norm_num, ?_⟩, GaloisField p (2 * f), inferInstance, inferInstance, ?_,
    ⟨MulEquiv.refl _⟩⟩
  · intro h; have := congrArg Prod.fst h; simp at this
  · rw [GaloisField.card p (2 * f) (by omega)]; ring

theorem isPSp4_of_lieModel {Gs : Type} [Group Gs] {p f : ℕ} (h : LieModel Gs .PSp 2 p f) :
    IVK.IsPSp4 Gs (p ^ f) := by
  rcases h with ⟨-, -, K, iK, fK, hK, he⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact ⟨K, iK, fK, hK, he⟩
  all_goals omega

theorem isLnEps_psl_of_lieModel {Gs : Type} [Group Gs] {p f : ℕ} (h : LieModel Gs .PSL 4 p f) :
    IVK.IsLnEps 4 Gs 1 (p ^ f) := by
  rcases h with ⟨-, -, K, iK, fK, hK, he⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact Or.inl ⟨rfl, K, iK, fK, hK, he⟩
  all_goals omega

theorem isLnEps_psu_of_lieModel {Gs : Type} [Group Gs] {p f : ℕ} (h : LieModel Gs .PSU 4 p f) :
    IVK.IsLnEps 4 Gs (-1) (p ^ f) := by
  rcases h with ⟨-, -, K, iK, fK, hK, he⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact Or.inr ⟨rfl, K, iK, fK, hK, he⟩
  all_goals omega

@[expose] def CompatAt {G Gs : Type} [Group G] [Group Gs] (z : G) (S : Subgroup G) (z' : Gs)
    (S' : Subgroup Gs) : Prop :=
  (center ↥S).map S.subtype = zpowers z ∧ (center ↥S').map S'.subtype = zpowers z' ∧
    ∃ ψ : ↥(layerTimesSylow z S) ≃* ↥(layerTimesSylow z' S'),
      (∀ x : ↥(layerTimesSylow z S), (x : G) ∈ S ↔ (ψ x : Gs) ∈ S') ∧
      (∀ x y : ↥(layerTimesSylow z S), (x : G) ∈ S → (y : G) ∈ S → orderOf (x : G) = 2 →
        orderOf (y : G) = 2 → (IsConj (x : G) (y : G) ↔ IsConj (ψ x : Gs) (ψ y : Gs)))

theorem compatAt_of_term7 (hMC : ModelCenter) (hEC : ECInter) {G : Type} [Group G] [Finite G] {z : G}
    {S : Subgroup G} {k : Kind} {q : ℕ} {w : G} (hctx : Stage2Ctx G z k S) (hout : Stage2Out G z k S)
    (hk : k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε) (h7 : Term7Out G z S q w)
    {Gs : Type} [Group Gs] [Finite Gs] {p f : ℕ} (hGs : IsClassicalModel Gs p f)
    (hmod : Model7 Gs q (w = 1)) :
    ∃ (S' : Sylow 2 Gs) (z' : Gs), orderOf z' = 2 ∧
      (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' ∧
      CompatAt z S z' (S' : Subgroup Gs) := by
  obtain ⟨K₁, K₂, hstd, hodd, h5, hK₁, hK₂, hT⟩ := h7
  obtain ⟨hL, hN⟩ := layerN_of_ecInter hEC hctx hout hk hstd
  obtain ⟨S'⟩ : Nonempty (Sylow 2 Gs) := inferInstance
  obtain ⟨z', hz'o, hcen⟩ := hMC Gs p f hGs S'
  have hC := hT Gs z' S' hmod hz'o hcen
  obtain ⟨ψ, hψS, hψf⟩ := compatIso_of_compat7 hL hN hC
  refine ⟨S', z', hz'o, hcen, ?_, hcen, ψ, hψS, hψf⟩
  exact center_eq_zpowers_of_equiv le_sup_right le_sup_right ψ hψS
    hctx.z_mem (fun s hs => hctx.S_comm_z hs) hctx.orderOf_z hz'o hcen


theorem oddCore_bot_of_psp4 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (h : Stage2Out G z Kind.psp4 S) : pPrimeCore 2 ↥(Cen z) = ⊥ :=
  h.oddCore (fun ε h' => by cases h')

theorem dvd_ordCompl_of_odd {n m : ℕ} (hn : Nat.Coprime 2 n) (h : n ∣ m) : n ∣ ordCompl[2] m := by
  have h2 : ordProj[2] m * ordCompl[2] m = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have hcop : Nat.Coprime n (ordProj[2] m) :=
    (Nat.Coprime.pow_left (m.factorization 2) hn).symm
  rw [← h2] at h
  exact hcop.dvd_of_dvd_mul_left h

theorem prime_ne_two_of_odd {p f q : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : q = p ^ f) (hodd : Odd q) :
    p ≠ 2 := by
  rintro rfl
  rw [hq] at hodd
  have : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact (Nat.not_even_iff_odd.2 hodd) this

theorem stageFiveClassical_of_psp4 (hMC : ModelCenter) (hEC : ECInter) (hMD : ModelsDisjoint)
    {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
    (hctx : Stage2Ctx G z Kind.psp4 S) (hout : Stage2Out G z Kind.psp4 S)
    (h7 : Term7Out G z S q 1) : StageFiveClassical G := by
  have h7' := h7
  obtain ⟨K₁, K₂, -, hodd, h5, ⟨F, iF, fF, hFq, -⟩, -, -⟩ := h7
  obtain ⟨p, f, hp, hf, hpf⟩ := exists_prime_pow_of_field F
  have hqpf : q = p ^ f := hFq.symm.trans hpf
  have hp2 : p ≠ 2 := prime_ne_two_of_odd hp hf hqpf hodd
  have h3 : 3 < p ^ f := by omega
  obtain ⟨Gs, iGs, fGs, hL⟩ := exists_model_psp p f hp hf h3
  have hGs : IsClassicalModel Gs p f := ⟨hp, hp2, h3, Or.inl hL⟩
  have hmod : Model7 Gs q ((1 : G) = 1) := Or.inl ⟨rfl, by rw [hqpf]; exact isPSp4_of_lieModel hL⟩
  obtain ⟨S', z', hz'o, hcenS', hcompat⟩ := compatAt_of_term7 hMC hEC hctx hout (Or.inl rfl) h7' hGs hmod
  refine ⟨Gs, iGs, Or.inl ⟨p, f, hp, hp2, h3, hL⟩, ?_⟩
  refine ⟨⟨p, f, hp, hp2, h3, Or.inl hL⟩, ?_⟩
  obtain ⟨S₀, hS₀⟩ := sylow_of_sylowTop hctx.sylow_top
  subst hS₀
  obtain ⟨hcz, hcz', ψ, hψS, hψf⟩ := hcompat
  refine ⟨S₀, z, S', z', hcz, hcz', ⟨ψ, hψS, hψf⟩, fun _ => oddCore_bot_of_psp4 hout, ?_⟩
  rintro ⟨p', f', hp', hp2', hLU⟩
  exfalso
  rcases hLU with h | h
  · exact (hMD Gs p f p' f' hp hp2 hp' hp2' hL).1 h
  · exact (hMD Gs p f p' f' hp hp2 hp' hp2' hL).2 h

theorem stageFiveClassical_of_l4NF (hMC : ModelCenter) (hEC : ECInter) (hMD : ModelsDisjoint)
    (hMO : ModelOddCore) {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {w : G} (hctx : Stage2Ctx G z (Kind.l4 ε) S)
    (hout : Stage2Out G z (Kind.l4 ε) S) (hq : Stage1L4 G z S ε q L₁ L₂)
    (hq4 : q % 4 = (if ε then 3 else 1)) (h7 : Term7Out G z S q w) (hw : w ≠ 1)
    (hmax : ∀ p f : ℕ, p.Prime → p ^ f = q → Max6A G p f) : StageFiveClassical G := by
  have h7' := h7
  obtain ⟨K₁, K₂, -, hodd, h5, ⟨F, iF, fF, hFq, -⟩, -, -⟩ := h7
  obtain ⟨p, f, hp, hf, hpf⟩ := exists_prime_pow_of_field F
  have hqpf : q = p ^ f := hFq.symm.trans hpf
  have hp2 : p ≠ 2 := prime_ne_two_of_odd hp hf hqpf hodd
  have h5' : 5 ≤ p ^ f := by omega
  have h3 : 3 < p ^ f := by omega
  have hmx := hmax p f hp hqpf.symm
  obtain ⟨hcyc, hdvd⟩ := hout.oddCoreL4 ε q L₁ L₂ rfl hq
  have key : ∀ (Gs : Type) [Group Gs] [Finite Gs], IsClassicalModel Gs p f →
      Model7 Gs q (w = 1) → ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨
        (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f)) →
      (Nat.card ↥(pPrimeCore 2 ↥(Cen z)) ∣ (if ε then q - 1 else q + 1) →
        ∀ (S' : Sylow 2 Gs) (z' : Gs), orderOf z' = 2 →
          (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' →
          Nat.card ↥(pPrimeCore 2 ↥(Cen z)) ∣ Nat.card ↥(pPrimeCore 2 ↥(centralizer ({z'} : Set Gs)))) →
      StageFiveClassical G := by
    intro Gs _ _ hGs hmod hLU hOdd
    obtain ⟨S', z', hz'o, hcenS', hcompat⟩ := compatAt_of_term7 hMC hEC hctx hout (Or.inr ⟨ε, rfl⟩) h7' hGs hmod
    refine ⟨Gs, inferInstance, Or.inr ⟨p, f, hp, hp2, h5', hLU, hmx⟩, ?_⟩
    refine ⟨⟨p, f, hp, hp2, h3, ?_⟩, ?_⟩
    · rcases hLU with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    obtain ⟨S₀, hS₀⟩ := sylow_of_sylowTop hctx.sylow_top
    subst hS₀
    obtain ⟨hcz, hcz', ψ, hψS, hψf⟩ := hcompat
    refine ⟨S₀, z, S', z', hcz, hcz', ⟨ψ, hψS, hψf⟩, ?_, ?_⟩
    · rintro ⟨p', f', hp', hp2', hLp⟩
      exfalso
      rcases hLU with ⟨-, h⟩ | ⟨-, h⟩
      · exact (hMD Gs p' f' p f hp' hp2' hp hp2 hLp).1 h
      · exact (hMD Gs p' f' p f hp' hp2' hp hp2 hLp).2 h
    · rintro -
      exact ⟨hcyc, hOdd hdvd S' z' hz'o hcenS'⟩
  have hodd2 : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
    CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z))
  cases ε
  ·
    have hq4' : q % 4 = 1 := by simpa using hq4
    have h8 : p ^ f % 8 ≠ 7 := by omega
    obtain ⟨Gs, iGs, fGs, hL⟩ := exists_model_psu p f hp hf
    exact key Gs ⟨hp, hp2, h3, Or.inr (Or.inr ⟨h8, hL⟩)⟩
      (Or.inr ⟨hw, Or.inr ⟨hq4', by rw [hqpf]; exact isLnEps_psu_of_lieModel hL⟩⟩)
      (Or.inr ⟨h8, hL⟩)
      (fun hd S' z' hz'o hcen => by
        have h1 := (hMO Gs p f S' z' ⟨hp, hp2, h3, Or.inr (Or.inr ⟨h8, hL⟩)⟩ hz'o hcen).2 h8 hL
        rw [h1]
        simp only [Bool.false_eq_true, ite_false] at hdvd
        rw [hqpf] at hdvd
        exact dvd_ordCompl_of_odd hodd2 hdvd)
  ·
    have hq4' : q % 4 = 3 := by simpa using hq4
    have h8 : p ^ f % 8 ≠ 1 := by omega
    obtain ⟨Gs, iGs, fGs, hL⟩ := exists_model_psl p f hp hf
    exact key Gs ⟨hp, hp2, h3, Or.inr (Or.inl ⟨h8, hL⟩)⟩
      (Or.inr ⟨hw, Or.inl ⟨hq4', by rw [hqpf]; exact isLnEps_psl_of_lieModel hL⟩⟩)
      (Or.inl ⟨h8, hL⟩)
      (fun hd S' z' hz'o hcen => by
        have h1 := (hMO Gs p f S' z' ⟨hp, hp2, h3, Or.inr (Or.inl ⟨h8, hL⟩)⟩ hz'o hcen).1 h8 hL
        rw [h1]
        simp only [ite_true] at hdvd
        rw [hqpf] at hdvd
        exact dvd_ordCompl_of_odd hodd2 hdvd)

end CFSG.GH74.GLS.Stage2.Final
