module

public import CFSG.LocalAnalysis.AGLEmbedding.SubnormalSymThreeDetermined
public import CFSG.LocalAnalysis.AGLEmbedding.SUPairInvolution
import CFSG.LocalAnalysis.AGLEmbedding.SUThreeTwoDetermined
import CFSG.LocalAnalysis.AGLEmbedding.SUThreeTwoQData
import CFSG.LocalAnalysis.AGLEmbedding.SUPairCommute
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Late.Uniqueness

public section

namespace CFSG.AGLEmbedding.SUDet

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b
open CFSG.AGLEmbedding.SUPair (Heis27)
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_two_subgroup (hO : CFSG.pCore 2 Y = ⊥) {D : Subgroup Y} [D.Normal]
    (hD3 : IsPGroup 3 D) {T₁ T₂ : Subgroup Y} (h₁ : IsSubnormal T₁ ⊤) (h₂ : IsSubnormal T₂ ⊤)
    (hT₁ : ∀ t ∈ T₁, ∃ a : ℕ, t ^ (2 ^ a) ∈ D) (hT₂ : ∀ t ∈ T₂, ∃ a : ℕ, t ^ (2 ^ a) ∈ D) :
    ∃ S : Subgroup Y, IsPGroup 2 S ∧ (∀ c ∈ S, (∀ d ∈ D, c * d = d * c) → c = 1) ∧
      ∀ t : Y, (t ∈ T₁ ∨ t ∈ T₂) → (∃ k : ℕ, t ^ (2 ^ k) = 1) → ∃ d ∈ D, d⁻¹ * t * d ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  set Q : Subgroup (Y ⧸ D) := pCoreOf 2 (⊤ : Subgroup (Y ⧸ D)) with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  have hTQ : ∀ {T : Subgroup Y}, IsSubnormal T ⊤ → (∀ t ∈ T, ∃ a : ℕ, t ^ (2 ^ a) ∈ D) →
      T.map π ≤ Q := by
    intro T hT hTD
    refine SubnormalCommute.le_pCoreOf_of_isSubnormal ?_ ?_
    · have := hT.map π
      rwa [map_top_of_surjective π hπs] at this
    · rintro ⟨x, ⟨t, ht, rfl⟩⟩
      obtain ⟨a, ha⟩ := hTD t ht
      refine ⟨a, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ha
  set O : Subgroup Y := Q.comap π with hOdef
  have hDO : D ≤ O := fun d hd => by
    show π d ∈ Q
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff d).mpr hd]
    exact one_mem Q
  obtain ⟨S₁⟩ : Nonempty (Sylow 2 ↥O) := inferInstance
  set S : Subgroup Y := (S₁ : Subgroup ↥O).map O.subtype with hS
  have hS2 : IsPGroup 2 S := S₁.isPGroup'.map O.subtype
  set φ : ↥O →* Y ⧸ D := π.comp O.subtype with hφ
  have hker : φ.ker = D.subgroupOf O := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf]
    rfl
  have hrange : φ.range = Q := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact x.2
    · intro q hq
      obtain ⟨y, rfl⟩ := hπs q
      exact ⟨⟨y, hq⟩, rfl⟩
  have hOcard : Nat.card O = Nat.card Q * Nat.card D := by
    have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker,
      Nat.card_congr (subgroupOfEquivOfLe hDO).toEquiv] at h1
    exact h1
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hQ2
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hD3
  have hS₁card : 2 ^ m ∣ Nat.card S := by
    rw [hS, card_map_of_injective O.subtype_injective]
    have hidx := (S₁ : Subgroup ↥O).card_mul_index
    have hnd : ¬ 2 ∣ (S₁ : Subgroup ↥O).index := S₁.not_dvd_index
    have hcop : Nat.Coprime (2 ^ m) (S₁ : Subgroup ↥O).index :=
      Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd)
    have hdvd : 2 ^ m ∣ Nat.card S₁ * (S₁ : Subgroup ↥O).index := by
      rw [hidx, hOcard, hm]
      exact dvd_mul_right _ _
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hDS : D ⊔ S = O := by
    refine eq_of_le_of_card_ge (sup_le hDO (map_subtype_le _)) ?_
    rw [hOcard, hm, hn]
    have h3 : 3 ^ n ∣ Nat.card ↥(D ⊔ S) := hn ▸ card_dvd_of_le le_sup_left
    have h2 : 2 ^ m ∣ Nat.card ↥(D ⊔ S) := hS₁card.trans (card_dvd_of_le le_sup_right)
    have hcop : Nat.Coprime (2 ^ m) (3 ^ n) :=
      Nat.Coprime.pow m n (by norm_num : Nat.Coprime 2 3)
    exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd h2 h3)
  refine ⟨S, hS2, ?_, ?_⟩
  ·
    intro c hcS hcD
    set K : Subgroup Y := centralizer (D : Set Y) ⊓ O with hK
    have hcK : c ∈ K := ⟨mem_centralizer_iff.mpr fun d hd => (hcD d hd).symm,
      map_subtype_le _ hcS⟩
    let ψ : ↥K →* ↥Q :=
      { toFun := fun k => ⟨π k, k.2.2⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp }
    have hψker : ψ.ker ≤ center ↥K := by
      intro k hk
      have hkD : (k : Y) ∈ D := by
        have : π k = 1 := congrArg Subtype.val hk
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      rw [mem_center_iff]
      intro k'
      apply Subtype.ext
      have := mem_centralizer_iff.mp k'.2.1 k hkD
      simpa using this.symm
    haveI : Group.IsNilpotent ↥Q := hQ2.isNilpotent
    haveI : Group.IsNilpotent ↥K := _root_.isNilpotent_of_ker_le_center ψ hψker
    obtain ⟨P₂⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
    have hP₂n : (P₂ : Subgroup ↥K).Normal := inferInstance
    have hcP : (⟨c, hcK⟩ : ↥K) ∈ (P₂ : Subgroup ↥K) := by
      obtain ⟨k, hk⟩ := hS2 ⟨c, hcS⟩
      have hck : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
      have h2 : IsPGroup 2 (zpowers (⟨c, hcK⟩ : ↥K)) := by
        rintro ⟨g, hg⟩
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hg
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        simp only [SubgroupClass.coe_pow, SubgroupClass.coe_zpow, OneMemClass.coe_one]
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hck, one_zpow]
      obtain ⟨P', hP'⟩ := h2.exists_le_sylow
      haveI := Sylow.unique_of_normal P₂ hP₂n
      have : P' = P₂ := Subsingleton.elim _ _
      rw [← this]
      exact hP' (mem_zpowers _)
    have hP₂core : (P₂ : Subgroup ↥K) ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hP₂n, P₂.isPGroup'⟩
    have hQn : Q.Normal := by
      rw [← normalizer_eq_top_iff, eq_top_iff]
      calc (⊤ : Subgroup (Y ⧸ D)) = normalizer ((⊤ : Subgroup (Y ⧸ D)) : Set (Y ⧸ D)) :=
            (normalizer_eq_top_iff.mpr inferInstance).symm
        _ ≤ _ := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 ⊤
    haveI : O.Normal := hQn.comap π
    haveI : K.Normal := inferInstance
    have hcore := CFSG.RankThree.PartTwo.Late.pCoreOf_le_pCore_of_isSubnormal 2
      (Subgroup.Normal.isSubnormal (inferInstance : K.Normal))
    have hmem : c ∈ CFSG.Open.pCore 2 Y := hcore ⟨⟨c, hcK⟩, hP₂core hcP, rfl⟩
    have : CFSG.Open.pCore 2 Y = ⊥ := hO
    rw [this] at hmem
    exact (mem_bot).mp hmem
  · intro t ht ht2
    have htO : t ∈ O := by
      rcases ht with ht | ht
      · exact hTQ h₁ hT₁ (mem_map_of_mem π ht)
      · exact hTQ h₂ hT₂ (mem_map_of_mem π ht)
    have h2t : IsPGroup 2 ((zpowers t).subgroupOf O) := by
      obtain ⟨k, hk⟩ := ht2
      rintro ⟨⟨g, hgO⟩, hg⟩
      have hg' : g ∈ zpowers t := by simpa [mem_subgroupOf] using hg
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hg'
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    obtain ⟨S₂, hS₂⟩ := h2t.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥O S₁ S₂
    have htg : (g : Y)⁻¹ * t * g ∈ S := by
      have h : (⟨t, htO⟩ : ↥O) ∈ (S₂ : Subgroup ↥O) :=
        hS₂ (mem_subgroupOf.mpr (mem_zpowers t))
      rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at h
      refine ⟨_, h, ?_⟩
      simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
    have hgmem : (g : Y) ∈ (↑(D ⊔ S) : Set Y) := by rw [hDS]; exact g.2
    rw [normal_mul] at hgmem
    obtain ⟨d, hd, s, hs, hgds⟩ := Set.mem_mul.mp hgmem
    refine ⟨d, hd, ?_⟩
    have e : d⁻¹ * t * d = s * ((g : Y)⁻¹ * t * g) * s⁻¹ := by rw [← hgds]; group
    rw [e]
    exact S.mul_mem (S.mul_mem hs htg) (S.inv_mem hs)

theorem eq_of_heis_of_not_mem {A Z B : Subgroup Y} (hH : Heis27 A Z) (hBA : B ≤ A) (hZB : Z ≤ B)
    {s x : Y} (hsB : s ∈ B) (hsZ : s ∉ Z) (hxB : x ∈ B) (hxs : ∀ k : ℤ, (s ^ k)⁻¹ * x ∉ Z) :
    B = A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcen : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z := hH.central
  have hdvd : Nat.card B ∣ 27 := hH.card ▸ card_dvd_of_le hBA
  have hZcard : Nat.card Z = 3 := hH.card_center
  have h3 : 3 ∣ Nat.card B := hZcard ▸ card_dvd_of_le hZB
  have hne3 : Nat.card B ≠ 3 := by
    intro h3'
    have : Z = B := eq_of_le_of_card_ge hZB (by rw [h3', hZcard])
    exact hsZ (this ▸ hsB)
  have hne9 : Nat.card B ≠ 9 := by
    intro h9
    set ZB := Z.subgroupOf B
    haveI : ZB.Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      have : (g : Y) * n * (g : Y)⁻¹ = n := by rw [← hcen _ hn _ (hBA g.2)]; group
      simpa [this] using hn⟩
    have hq := card_eq_card_quotient_mul_card_subgroup ZB
    rw [h9, Nat.card_congr (subgroupOfEquivOfLe hZB).toEquiv, hZcard] at hq
    have hq3 : Nat.card (↥B ⧸ ZB) = 3 := by omega
    have hsq : (QuotientGroup.mk (⟨s, hsB⟩ : ↥B) : ↥B ⧸ ZB) ≠ 1 := by
      rw [Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hsZ
    have htop := zpowers_eq_top_of_prime_card hq3 hsq
    have hxq : (QuotientGroup.mk (⟨x, hxB⟩ : ↥B) : ↥B ⧸ ZB) ∈
        zpowers (QuotientGroup.mk (⟨s, hsB⟩ : ↥B) : ↥B ⧸ ZB) := by
      rw [htop]; exact mem_top _
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxq
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_subgroupOf] at hk
    exact hxs k (by simpa using hk)
  have h27 : Nat.card B = 1 ∨ Nat.card B = 3 ∨ Nat.card B = 9 ∨ Nat.card B = 27 := by
    have : Nat.card B ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [hd] at this
    simpa using this
  have hB27 : Nat.card B = 27 := by
    rcases h27 with h1 | h1 | h1 | h1
    · rw [h1] at h3; norm_num at h3
    · exact absurd h1 hne3
    · exact absurd h1 hne9
    · exact h1
  exact eq_of_le_of_card_ge hBA (by rw [hB27, hH.card])

theorem inv_mod_center {A Z : Subgroup Y} (hH : Heis27 A Z) {u s d : Y}
    (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A) (huZ : ∀ z ∈ Z, u * z = z * u) (hs : s ∈ A) (hd : d ∈ A)
    (hsd : s * d ≠ d * s) (hus : u * s * u⁻¹ = s⁻¹) (hud : u * d * u⁻¹ = d⁻¹) :
    ∀ a ∈ A, u * a * u⁻¹ * a ∈ Z := by
  have hcen : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z := hH.central
  let B : Subgroup Y :=
    { carrier := {a | a ∈ A ∧ u * a * u⁻¹ * a ∈ Z}
      one_mem' := ⟨A.one_mem, by simp [Z.one_mem]⟩
      mul_mem' := by
        rintro a b ⟨ha, hwa⟩ ⟨hb, hwb⟩
        refine ⟨A.mul_mem ha hb, ?_⟩
        obtain ⟨wa, hwaZ, hwa'⟩ : ∃ w ∈ Z, u * a * u⁻¹ = w * a⁻¹ := ⟨_, hwa, by group⟩
        obtain ⟨wb, hwbZ, hwb'⟩ : ∃ w ∈ Z, u * b * u⁻¹ = w * b⁻¹ := ⟨_, hwb, by group⟩
        have e : u * (a * b) * u⁻¹ * (a * b) = wa * (a⁻¹ * wb) * (b⁻¹ * a * b) := by
          calc u * (a * b) * u⁻¹ * (a * b) = (u * a * u⁻¹) * (u * b * u⁻¹) * (a * b) := by
                group
            _ = _ := by rw [hwa', hwb']; group
        rw [e, ← hcen wb hwbZ _ (A.inv_mem ha)]
        have e2 : wa * (wb * a⁻¹) * (b⁻¹ * a * b) = (wa * wb) * (a⁻¹ * b⁻¹ * a⁻¹⁻¹ * b⁻¹⁻¹) := by
          group
        rw [e2]
        exact Z.mul_mem (Z.mul_mem hwaZ hwbZ) (hH.comm_mem _ (A.inv_mem ha) _ (A.inv_mem hb))
      inv_mem' := by
        rintro a ⟨ha, hwa⟩
        refine ⟨A.inv_mem ha, ?_⟩
        obtain ⟨wa, hwaZ, hwa'⟩ : ∃ w ∈ Z, u * a * u⁻¹ = w * a⁻¹ := ⟨_, hwa, by group⟩
        have e : u * a⁻¹ * u⁻¹ * a⁻¹ = a * wa⁻¹ * a⁻¹ := by
          calc u * a⁻¹ * u⁻¹ * a⁻¹ = (u * a * u⁻¹)⁻¹ * a⁻¹ := by group
            _ = a * wa⁻¹ * a⁻¹ := by rw [hwa']; group
        rw [e, ← hcen _ (Z.inv_mem hwaZ) _ ha]
        simpa using Z.inv_mem hwaZ }
  have hBA : B ≤ A := fun a ha => ha.1
  have hZB : Z ≤ B := fun z hz => ⟨hH.le hz, by
    have : u * z * u⁻¹ * z = z * z := by rw [huZ z hz]; group
    rw [this]; exact Z.mul_mem hz hz⟩
  have hsB : s ∈ B := ⟨hs, by rw [hus, inv_mul_cancel]; exact Z.one_mem⟩
  have hdB : d ∈ B := ⟨hd, by rw [hud, inv_mul_cancel]; exact Z.one_mem⟩
  have hsZ : s ∉ Z := fun h => hsd (hcen s h d hd)
  have hds : ∀ k : ℤ, (s ^ k)⁻¹ * d ∉ Z := by
    intro k hk
    apply hsd
    have hdk : d = s ^ k * ((s ^ k)⁻¹ * d) := by group
    have hc := hcen _ hk s hs
    rw [hdk]
    calc s * (s ^ k * ((s ^ k)⁻¹ * d)) = s ^ k * (s * ((s ^ k)⁻¹ * d)) := by group
      _ = s ^ k * (((s ^ k)⁻¹ * d) * s) := by rw [hc]
      _ = s ^ k * ((s ^ k)⁻¹ * d) * s := by group
  have := eq_of_heis_of_not_mem hH hBA hZB hsB hsZ hdB hds
  intro a ha
  rw [← this] at ha
  exact ha.2

theorem card_oUpperTwo_le_of_symThree {T : Subgroup Y} (e : ↥T ≃* Equiv.Perm (Fin 3)) :
    Nat.card (oUpperTwo T) ≤ 3 := by
  classical
  have hmem := fun x (hx : x ∈ oUpperTwo T) => SymThreeDetermined.cube_of_mem_oUpperTwo e hx
  let ι : ↥(oUpperTwo T) → {σ : Equiv.Perm (Fin 3) // σ ^ 3 = 1} := fun x =>
    ⟨e ⟨x, (hmem x x.2).1⟩, by
      rw [← map_pow]
      have : (⟨(x : Y), (hmem x x.2).1⟩ : ↥T) ^ 3 = 1 := Subtype.ext (by simpa using (hmem x x.2).2)
      rw [this, map_one]⟩
  have hι : Function.Injective ι := by
    intro x y h
    have h1 := congrArg Subtype.val h
    have h2 := e.injective h1
    exact Subtype.ext (by simpa using congrArg Subtype.val h2)
  have h3 : Nat.card {σ : Equiv.Perm (Fin 3) // σ ^ 3 = 1} = 3 := by
    rw [Nat.card_eq_fintype_card]; decide
  exact h3 ▸ Nat.card_le_card_of_injective ι hι

open SUPair in
theorem subnormalSUThreeTwoDetermined_holds : SubnormalSUThreeTwoDetermined := by
  intro Y _ _ hO T₁ T₂ hs₁ hs₂ hb₁ hb₂ hE₁ hA
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu₁ := hb₁.resolve_left (fun ⟨e⟩ => hE₁.false e)
  obtain ⟨s₁, d₁, z₁, f₁, g₁, -, -, hf₁T, hf₁4, hs₁u, hd₁u, hz₁c, hH₁, hs₁O, hd₁O, hsd₁, hg₁T,
    hf₁2, hg₁2, hg₁f, hT₁c⟩ := SUQ.exists_qdata_of_su hu₁
  set A := oUpperTwo T₁ with hAdef
  have hu₂ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (↥T₂ ≃* ↥(CFSG.Open.StatedSU 3 2 K)) := by
    rcases hb₂ with ⟨e₂⟩ | hu₂
    · exfalso
      have h := card_oUpperTwo_le_of_symThree e₂.some
      rw [← hA, hH₁.card] at h
      omega
    · exact hu₂
  obtain ⟨s₂, d₂, z₂, f₂, g₂, -, -, hf₂T, hf₂4, hs₂u, hd₂u, hz₂c, hH₂, hs₂O, hd₂O, hsd₂, hg₂T,
    hf₂2, hg₂2, hg₂f, hT₂c⟩ := SUQ.exists_qdata_of_su hu₂
  rw [← hA] at hH₂ hs₂O hd₂O
  have h₁ : IsSubnormal T₁ ⊤ := IsSubnormal.of_mathlib hs₁
  have h₂ : IsSubnormal T₂ ⊤ := IsSubnormal.of_mathlib hs₂
  have hAT₁ : A ≤ T₁ := oUpperTwo_le T₁
  have hAT₂ : A ≤ T₂ := by rw [hA]; exact oUpperTwo_le T₂
  set D : Subgroup Y := pCoreOf 3 (⊤ : Subgroup Y) with hDdef
  have hD3 : IsPGroup 3 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 ⊤
  have hDN : ∀ g : Y, g ∈ normalizer (D : Set Y) := fun g =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 3 ⊤ (le_normalizer (mem_top g))
  haveI hDn : D.Normal := normalizer_eq_top_iff.mp (eq_top_iff.mpr fun g _ => hDN g)
  have hD3el : ∀ x ∈ D, ∃ k : ℕ, x ^ (3 ^ k) = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hD3 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hA3 : IsPGroup 3 A := fun ⟨a, ha⟩ => ⟨1, Subtype.ext (by simpa using hH₁.cube a ha)⟩
  have hAD : A ≤ D := SubnormalCommute.le_pCoreOf_of_isSubnormal (isSubnormal_oUpperTwo h₁) hA3
  have hD2 : ¬ 2 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hD3
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hcommT : ∀ {T : Subgroup Y}, IsSubnormal T ⊤ → ∀ {t : Y}, t ∈ T →
      (∃ k : ℕ, t ^ (2 ^ k) = 1) → ⁅D, zpowers t⁆ ≤ oUpperTwo T := by
    intro T hT t ht hk
    obtain ⟨k, hk⟩ := hk
    have h2t : IsPGroup 2 (zpowers t) := by
      rintro ⟨g, hg⟩
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
      refine ⟨k, Subtype.ext ?_⟩
      change (t ^ n) ^ 2 ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    have hE := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2
      Nat.prime_two (zpowers t) D h2t hD2 (fun g _ => hDN g)
    have hET := SubnormalCommute.commutator_zpowers_le_of_isSubnormal hT hE ht le_top
    intro x hx
    have hxD : x ∈ D := commutator_le_left D (zpowers t) hx
    obtain ⟨k', hk'⟩ := hD3el x hxD
    exact subset_closure ⟨hET hx,
      (Odd.pow (by decide : Odd 3)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hk')⟩
  have hcomm₁ : ∀ {t : Y}, t ∈ T₁ → (∃ k : ℕ, t ^ (2 ^ k) = 1) → ⁅D, zpowers t⁆ ≤ A :=
    fun ht hk => hcommT h₁ ht hk
  have hcomm₂ : ∀ {t : Y}, t ∈ T₂ → (∃ k : ℕ, t ^ (2 ^ k) = 1) → ⁅D, zpowers t⁆ ≤ A :=
    fun ht hk => by rw [hA]; exact hcommT h₂ ht hk
  have hsq_mem : ∀ {B : Subgroup Y} {u s : Y}, s ∈ B → u * s * u⁻¹ = s⁻¹ → s ^ 3 = 1 →
      s ∈ ⁅B, zpowers u⁆ := by
    intro B u s hs hus hs3
    have h1 : s * u * s⁻¹ * u⁻¹ = s ^ 2 := by
      rw [show s * u * s⁻¹ * u⁻¹ = s * (u * s * u⁻¹)⁻¹ by group, hus, inv_inv, sq]
    have h2 : s ^ 2 ∈ ⁅B, zpowers u⁆ := by
      have := commutator_mem_commutator hs (mem_zpowers u)
      rwa [commutatorElement_def, h1] at this
    have h3 : s = (s ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hs3, one_mul]
    rw [h3]
    exact pow_mem h2 2
  have hDu : ⁅D, zpowers (f₁ ^ 2)⁆ = A :=
    eq_of_le_of_noncomm hH₁ (hcomm₁ (pow_mem hf₁T 2) ⟨1, by rw [pow_one, ← pow_mul]; exact hf₁4⟩)
      (hsq_mem (hAD hs₁O) hs₁u (hH₁.cube _ hs₁O)) (hsq_mem (hAD hd₁O) hd₁u (hH₁.cube _ hd₁O))
      hsd₁
  have hAN : D ≤ normalizer (A : Set Y) := hDu ▸ le_normalizer_commutator_zpowers (hDN _)
  have hnorm : ∀ x ∈ D, ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun x hx a ha =>
    (mem_normalizer_iff.mp (hAN hx) a).mp ha
  set Z := zpowers z₁ with hZdef
  have hz3 : orderOf z₁ = 3 := by
    have := hH₁.card_center
    rwa [Nat.card_zpowers] at this
  have hZeq : zpowers z₂ = Z := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr ?_) ?_
    · exact hH₁.center_le z₂ (hH₂.le (mem_zpowers z₂))
        (fun a ha => hH₂.central z₂ (mem_zpowers z₂) a ha)
    · rw [hH₁.card_center, hH₂.card_center]
  have hZT₁ : ∀ x ∈ T₁, ∀ z ∈ Z, x * z = z * x := by
    intro x hx z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (hz₁c x hx) k : Commute (z₁ ^ k) x)).eq.symm
  have hZT₂ : ∀ x ∈ T₂, ∀ z ∈ Z, x * z = z * x := by
    intro x hx z hz
    rw [← hZeq] at hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (hz₂c x hx) k : Commute (z₂ ^ k) x)).eq.symm
  have hDZ : ∀ x ∈ D, ∀ z ∈ Z, x * z = z * x := by
    have hxz : ∀ x ∈ D, x * z₁ = z₁ * x := by
      intro x hx
      have hxz : x * z₁ * x⁻¹ ∈ zpowers z₁ := by
        apply hH₁.center_le
        · exact hnorm x hx z₁ (hH₁.le (mem_zpowers z₁))
        · intro a ha
          have ha' : x⁻¹ * a * x ∈ A := by
            have := hnorm x⁻¹ (inv_mem hx) a ha
            simpa using this
          have hc := hH₁.central z₁ (mem_zpowers z₁) _ ha'
          calc x * z₁ * x⁻¹ * a = x * (z₁ * (x⁻¹ * a * x)) * x⁻¹ := by group
            _ = x * ((x⁻¹ * a * x) * z₁) * x⁻¹ := by rw [hc]
            _ = a * (x * z₁ * x⁻¹) := by group
      obtain ⟨k, hk⟩ := hD3el x hx
      exact commute_of_conj_mem_zpowers_three hz3 hk hxz
    intro x hx z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact ((Commute.zpow_right (hxz x hx) k : Commute x (z₁ ^ k))).eq
  obtain ⟨X₁, hX₁6, hX₁T, hX₁sq, hX₁4, hX₁A, -⟩ := SUQ.exists_six_roots hf₁T hg₁T hf₁4 hf₁2
    hg₁2 hg₁f hAT₁ hH₁.cube hH₁.card hT₁c
  obtain ⟨X₂, -, hX₂T, hX₂sq, hX₂4, -, hX₂gen⟩ := SUQ.exists_six_roots hf₂T hg₂T hf₂4 hf₂2
    hg₂2 hg₂f hAT₂ hH₁.cube hH₁.card hT₂c
  have hinv₁ : ∀ a ∈ A, f₁ ^ 2 * a * (f₁ ^ 2)⁻¹ * a ∈ Z :=
    inv_mod_center hH₁ (fun a ha => conj_mem_oUpperTwo (pow_mem hf₁T 2) ha)
      (fun z hz => hZT₁ _ (pow_mem hf₁T 2) z hz) hs₁O hd₁O hsd₁ hs₁u hd₁u
  have hinv₂ : ∀ a ∈ A, f₂ ^ 2 * a * (f₂ ^ 2)⁻¹ * a ∈ Z := by
    refine inv_mod_center hH₁ (fun a ha => ?_) (fun z hz => hZT₂ _ (pow_mem hf₂T 2) z hz) hs₂O
      hd₂O hsd₂ hs₂u hd₂u
    rw [hA] at ha ⊢
    exact conj_mem_oUpperTwo (pow_mem hf₂T 2) ha
  have hT₁D : ∀ t ∈ T₁, ∃ a : ℕ, t ^ (2 ^ a) ∈ D := fun t ht => by
    obtain ⟨a, ha⟩ := exists_two_pow_mem ht
    exact ⟨a, hAD ha⟩
  have hT₂D : ∀ t ∈ T₂, ∃ a : ℕ, t ^ (2 ^ a) ∈ D := fun t ht => by
    obtain ⟨a, ha⟩ := exists_two_pow_mem ht
    rw [← hA] at ha
    exact ⟨a, hAD ha⟩
  obtain ⟨S, hS2, hCS, hconj⟩ := exists_two_subgroup hO hD3 h₁ h₂ hT₁D hT₂D
  have hδex : ∀ t : Y, ∃ d : Y, ((t ∈ T₁ ∨ t ∈ T₂) ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1) →
      d ∈ D ∧ d⁻¹ * t * d ∈ S := by
    intro t
    by_cases hc : (t ∈ T₁ ∨ t ∈ T₂) ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1
    · obtain ⟨d, hd, hdS⟩ := hconj t hc.1 hc.2
      exact ⟨d, fun _ => ⟨hd, hdS⟩⟩
    · exact ⟨1, fun h => absurd h hc⟩
  choose δ hδ using hδex
  have h2el : ∀ {t : Y}, t ^ 4 = 1 → ∃ k : ℕ, t ^ (2 ^ k) = 1 := fun h => ⟨2, h⟩
  have hgood : ∀ {T : Subgroup Y} {f t : Y}, (T = T₁ ∨ T = T₂) → t ∈ T → t ^ 4 = 1 →
      t ^ 2 = f ^ 2 → (∀ a ∈ A, f ^ 2 * a * (f ^ 2)⁻¹ * a ∈ Z) →
      Good D A Z S ((δ t)⁻¹ * t * δ t) ∧ (δ t)⁻¹ * t * δ t ∈ T ∧
        (δ t)⁻¹ * t * δ t * t⁻¹ ∈ A := by
    intro T f t hT ht ht4 htf hinv
    have hTT : t ∈ T₁ ∨ t ∈ T₂ := by
      rcases hT with rfl | rfl
      · exact Or.inl ht
      · exact Or.inr ht
    obtain ⟨hdD, hdS⟩ := hδ t ⟨hTT, h2el ht4⟩
    have hcommT' : ∀ {x : Y}, x ∈ T → (∃ k : ℕ, x ^ (2 ^ k) = 1) → ⁅D, zpowers x⁆ ≤ A := by
      intro x hx hk
      rcases hT with rfl | rfl
      · exact hcomm₁ hx hk
      · exact hcomm₂ hx hk
    have hAT : A ≤ T := by
      rcases hT with rfl | rfl
      · exact hAT₁
      · exact hAT₂
    have hOT : oUpperTwo T = A := by
      rcases hT with rfl | rfl
      · rfl
      · exact hA.symm
    have hZT : ∀ x ∈ T, ∀ z ∈ Z, x * z = z * x := by
      rcases hT with rfl | rfl
      · exact hZT₁
      · exact hZT₂
    have hya : (δ t)⁻¹ * t * δ t * t⁻¹ ∈ A := by
      have : (δ t)⁻¹ * t * δ t * t⁻¹ = ⁅(δ t)⁻¹, t⁆ := by rw [commutatorElement_def]; group
      rw [this]
      exact hcommT' ht (h2el ht4) (commutator_mem_commutator (inv_mem hdD) (mem_zpowers t))
    have hyT : (δ t)⁻¹ * t * δ t ∈ T := by
      have : (δ t)⁻¹ * t * δ t = ((δ t)⁻¹ * t * δ t * t⁻¹) * t := by group
      rw [this]
      exact T.mul_mem (hAT hya) ht
    have hy4 : ((δ t)⁻¹ * t * δ t) ^ 4 = 1 := by
      rw [show (δ t)⁻¹ * t * δ t = (δ t)⁻¹ * t * (δ t)⁻¹⁻¹ by rw [inv_inv], conj_pow, ht4]
      group
    refine ⟨⟨hdS, ?_, ?_, ?_, ?_, ?_⟩, hyT, hya⟩
    · intro a ha
      rw [← hOT] at ha ⊢
      exact conj_mem_oUpperTwo hyT ha
    · intro a ha
      rw [← hOT] at ha ⊢
      have := conj_mem_oUpperTwo (T.inv_mem hyT) ha
      simpa using this
    · intro z hz
      exact hZT _ hyT z hz
    · intro e he
      have h := hcommT' hyT (h2el hy4) (commutator_mem_commutator he (mem_zpowers _))
      rw [commutatorElement_def] at h
      have := A.inv_mem h
      have e' : (e * ((δ t)⁻¹ * t * δ t) * e⁻¹ * ((δ t)⁻¹ * t * δ t)⁻¹)⁻¹ =
          ((δ t)⁻¹ * t * δ t) * e * ((δ t)⁻¹ * t * δ t)⁻¹ * e⁻¹ := by group
      rwa [e'] at this
    · intro a ha
      have ha' : δ t * a * (δ t)⁻¹ ∈ A := hnorm (δ t) hdD a ha
      obtain ⟨w, hwZ, hw⟩ : ∃ w ∈ Z, f ^ 2 * (δ t * a * (δ t)⁻¹) * (f ^ 2)⁻¹ =
          w * (δ t * a * (δ t)⁻¹)⁻¹ := ⟨_, hinv _ ha', by group⟩
      have hy2 : ((δ t)⁻¹ * t * δ t) ^ 2 = (δ t)⁻¹ * f ^ 2 * δ t := by
        rw [← htf]; simp only [sq]; group
      have hdw : (δ t)⁻¹ * w * δ t = w := by
        rw [hDZ _ (inv_mem hdD) w hwZ]; group
      have e : ((δ t)⁻¹ * t * δ t) ^ 2 * a * (((δ t)⁻¹ * t * δ t) ^ 2)⁻¹ * a = w := by
        calc ((δ t)⁻¹ * t * δ t) ^ 2 * a * (((δ t)⁻¹ * t * δ t) ^ 2)⁻¹ * a =
              (δ t)⁻¹ * (f ^ 2 * (δ t * a * (δ t)⁻¹) * (f ^ 2)⁻¹) * δ t * a := by
                rw [hy2]; group
          _ = (δ t)⁻¹ * (w * (δ t * a * (δ t)⁻¹)⁻¹) * δ t * a := by rw [hw]
          _ = (δ t)⁻¹ * w * δ t := by group
          _ = w := hdw
      rw [e]
      exact hwZ
  have hg₁ := fun t (ht : t ∈ X₁) =>
    hgood (Or.inl rfl) (hX₁T t ht) (hX₁4 t ht) (hX₁sq t ht) hinv₁
  have hg₂ := fun t (ht : t ∈ X₂) =>
    hgood (Or.inr rfl) (hX₂T t ht) (hX₂4 t ht) (hX₂sq t ht) hinv₂
  have hinj : Set.InjOn (fun t => (δ t)⁻¹ * t * δ t) (X₁ : Set Y) := by
    intro t ht t' ht' he
    obtain ⟨-, -, ha⟩ := hg₁ t ht
    obtain ⟨-, -, ha'⟩ := hg₁ t' ht'
    simp only at he
    apply hX₁A t ht t' ht'
    have : t' * t⁻¹ = ((δ t')⁻¹ * t' * δ t' * t'⁻¹)⁻¹ * ((δ t)⁻¹ * t * δ t * t⁻¹) := by
      rw [he]; group
    rw [this]
    exact A.mul_mem (A.inv_mem ha') ha
  set X₁' := X₁.image (fun t => (δ t)⁻¹ * t * δ t) with hX₁'
  have hX₁'6 : X₁'.card = 6 := by rw [hX₁', Finset.card_image_of_injOn hinj, hX₁6]
  have hX₁'g : ∀ y ∈ X₁', Good D A Z S y := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    exact (hg₁ t ht).1
  have hsZ : s₁ ∉ Z := fun h => hsd₁ (hH₁.central s₁ h d₁ hd₁O)
  have hX₂T₁ : ∀ t ∈ X₂, t ∈ T₁ := by
    intro t ht
    obtain ⟨hgy, -, hya⟩ := hg₂ t ht
    have hmem := mem_of_good hH₁ hS2 hCS hs₁O hsZ X₁' hX₁'6 hX₁'g hgy
    obtain ⟨t₁, ht₁, he⟩ := Finset.mem_image.mp hmem
    obtain ⟨-, hyT₁, -⟩ := hg₁ t₁ ht₁
    have hφT₁ : (δ t)⁻¹ * t * δ t ∈ T₁ := he ▸ hyT₁
    have : t = ((δ t)⁻¹ * t * δ t * t⁻¹)⁻¹ * ((δ t)⁻¹ * t * δ t) := by group
    rw [this]
    exact T₁.mul_mem (hAT₁ (A.inv_mem hya)) hφT₁
  have hle : T₂ ≤ T₁ := by
    rw [← hX₂gen, closure_le]
    exact Set.union_subset hAT₁ (fun t ht => hX₂T₁ t ht)
  exact (eq_of_le_of_card_ge hle (by rw [hT₁c, hT₂c])).symm

end CFSG.AGLEmbedding.SUDet
