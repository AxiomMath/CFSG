module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.Quasithin.Background.SmithB45TorF4W
public import CFSG.HardMathSupport.Malle.LocalAction.CenterFromAbelianSylow
import CFSG.RankThree.PartOne.K128.ReeShape
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Generic

lemma isElemAbelian_iff {p : ℕ} {G : Type*} [Group G] (E : Subgroup G) :
    IsElemAbelian p E ↔ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ x ∈ E, x ^ p = 1 := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨fun a ha b hb => ?_, h⟩
    have := hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  · rintro ⟨hc, h⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, h⟩

lemma isElemAbelian_map' {p : ℕ} {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {E : Subgroup G} (h : IsElemAbelian p E) : IsElemAbelian p (E.map f) :=
  CFSG.Open.IsElemAbelian.map h _

variable {Y : Type} [Group Y]

lemma centralizer_map_conj (g : Y) (H : Subgroup Y) :
    Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.centralizer (H : Set Y)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_map, SetLike.mem_coe]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, fun h hh => ?_, by simp [MulAut.conj_apply]; group⟩
    have := hx (g * h * g⁻¹) ⟨h, hh, by simp [MulAut.conj_apply]⟩
    calc h * (g⁻¹ * x * g) = g⁻¹ * (g * h * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * h * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * x * g * h := by group
  · rintro ⟨x', hx', rfl⟩ _ ⟨h, hh, rfl⟩
    have := hx' h hh
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    calc g * h * g⁻¹ * (g * x' * g⁻¹) = g * (h * x') * g⁻¹ := by group
      _ = g * (x' * h) * g⁻¹ := by rw [this]
      _ = g * x' * g⁻¹ * (g * h * g⁻¹) := by group

lemma centerOf_map_conj (g : Y) (H : Subgroup Y) :
    centerOf (H.map (MulAut.conj g).toMonoidHom) =
      (centerOf H).map (MulAut.conj g).toMonoidHom := by
  unfold centerOf
  rw [centralizer_map_conj, Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

end Generic

section SylowInf

variable {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal] {p : ℕ} [Fact p.Prime]

omit [Finite Y] [Fact p.Prime] in
lemma mem_smul_sylow {g : Y} {S : Sylow p Y} {x : Y} :
    x ∈ ((g • S : Sylow p Y) : Subgroup Y) ↔ g⁻¹ * x * g ∈ (S : Subgroup Y) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

omit [Finite Y] [Fact p.Prime] in
lemma smul_sylow_inf_eq (S : Sylow p Y) (g : Y) :
    ((g • S : Sylow p Y) : Subgroup Y) ⊓ K =
      ((S : Subgroup Y) ⊓ K).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_inf, mem_smul_sylow, Subgroup.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨g⁻¹ * x * g, Subgroup.mem_inf.2 ⟨h1, ?_⟩, by simp [MulAut.conj_apply]; group⟩
    exact Subgroup.Normal.conj_mem' inferInstance x h2 g
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hy
    have e : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      simp [MulAut.conj_apply]; group
    refine ⟨by rw [e]; exact h1, ?_⟩
    simpa [MulAut.conj_apply] using Subgroup.Normal.conj_mem inferInstance y h2 g

omit [Finite Y] [Fact p.Prime] in
lemma card_smul_sylow_inf (S : Sylow p Y) (g : Y) :
    Nat.card ↥(((g • S : Sylow p Y) : Subgroup Y) ⊓ K) = Nat.card ↥((S : Subgroup Y) ⊓ K) := by
  rw [smul_sylow_inf_eq, Subgroup.card_map_of_injective (MulAut.conj g).injective]

lemma card_sylow_inf_normal (S : Sylow p Y) :
    Nat.card ↥((S : Subgroup Y) ⊓ K) = p ^ (Nat.card K).factorization p := by
  obtain ⟨Q0⟩ : Nonempty (Sylow p K) := inferInstance
  obtain ⟨Q, hQ⟩ := Sylow.exists_comap_subtype_eq (p := p) Q0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q S
  rw [← hg, card_smul_sylow_inf]
  have h1 : Nat.card ↥((Q : Subgroup Y) ⊓ K) = Nat.card ↥((Q : Subgroup Y).comap K.subtype) := by
    have : ((Q : Subgroup Y) ⊓ K).subgroupOf K = (Q : Subgroup Y).comap K.subtype := by
      ext x; simp [Subgroup.mem_subgroupOf]
    rw [← this]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  rw [h1, hQ, Sylow.card_eq_multiplicity]

lemma exists_sylow_eq_inf (S : Sylow p Y) :
    ∃ Q : Sylow p K, (Q : Subgroup K) = ((S : Subgroup Y) ⊓ K).subgroupOf K := by
  refine ⟨Sylow.ofCard (((S : Subgroup Y) ⊓ K).subgroupOf K) ?_, rfl⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
    card_sylow_inf_normal]

lemma card_sylow_eq_mul_inf (hidx : K.index = p) (S : Sylow p Y) :
    Nat.card (S : Subgroup Y) = p * Nat.card ↥((S : Subgroup Y) ⊓ K) := by
  rw [Sylow.card_eq_multiplicity, card_sylow_inf_normal]
  have hcard : Nat.card Y = Nat.card K * p := by
    rw [← hidx, Subgroup.card_mul_index]
  rw [hcard, Nat.factorization_mul Nat.card_pos.ne' (Fact.out : p.Prime).ne_zero]
  simp [(Fact.out : p.Prime).factorization_self, pow_succ, mul_comm]

end SylowInf

section Homocyclic

abbrev Hc : Type := Fin 2 → Multiplicative (ZMod 25)

lemma card_pow_five_ker : Nat.card (powMonoidHom 5 : Hc →* Hc).ker = 25 := by
  have : Nat.card (powMonoidHom 5 : Hc →* Hc).ker = Nat.card {f : Hc // f ^ 5 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun f => by simp [MonoidHom.mem_ker])
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

lemma comm_of_homocyclic {G : Type*} [Group G] {A : Subgroup G} (e : A ≃* Hc) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  have h : e ⟨a, ha⟩ * e ⟨b, hb⟩ = e ⟨b, hb⟩ * e ⟨a, ha⟩ := mul_comm _ _
  rw [← map_mul, ← map_mul] at h
  exact congrArg Subtype.val (e.injective h)

lemma eq_of_exponent_five_of_homocyclic {G : Type*} [Group G] {A E E' : Subgroup G}
    (e : A ≃* Hc) (hE : E ≤ A) (hE' : E' ≤ A) (h : ∀ x ∈ E, x ^ 5 = 1)
    (h' : ∀ x ∈ E', x ^ 5 = 1) (hc : Nat.card E = 25) (hc' : Nat.card E' = 25) : E = E' := by
  have key : ∀ F : Subgroup G, F ≤ A → (∀ x ∈ F, x ^ 5 = 1) → Nat.card F = 25 →
      (F.subgroupOf A).map e.toMonoidHom = (powMonoidHom 5 : Hc →* Hc).ker := by
    intro F hF h5 hc
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨a, ha, rfl⟩
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have : a ^ 5 = 1 := Subtype.ext (h5 a ha)
      show e.toMonoidHom a ^ 5 = 1
      rw [← map_pow, this, map_one]
    · rw [card_pow_five_ker, Subgroup.card_map_of_injective e.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv, hc]
  have := (key E hE h hc).trans (key E' hE' h' hc').symm
  have h2 := Subgroup.map_injective e.injective this
  ext x
  constructor
  · intro hx
    have : (⟨x, hE hx⟩ : A) ∈ E'.subgroupOf A := h2 ▸ (Subgroup.mem_subgroupOf.2 hx)
    exact Subgroup.mem_subgroupOf.1 this
  · intro hx
    have : (⟨x, hE' hx⟩ : A) ∈ E.subgroupOf A := h2.symm ▸ (Subgroup.mem_subgroupOf.2 hx)
    exact Subgroup.mem_subgroupOf.1 this

variable {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal]

lemma sylow_inf_homocyclic (hshape : CFSG.RankThree.PartOne.K1214.SylowShape 5 2 2 K)
    (S : Sylow 5 Y) : Nonempty (↥((S : Subgroup Y) ⊓ K) ≃* Hc) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_inf K S
  obtain ⟨e⟩ := hshape (Q : Subgroup K) Q.isPGroup' Q.not_dvd_index
  exact ⟨((Subgroup.subgroupOfEquivOfLe (inf_le_right :
    (S : Subgroup Y) ⊓ K ≤ K)).symm.trans (MulEquiv.subgroupCongr hQ.symm)).trans e⟩

end Homocyclic

section GL23

open CFSG.Quasithin.B45Tor
open scoped commutatorElement

variable {G G' : Type*} [Group G] [Group G'] (φ : G →* G') {R : Subgroup G}

lemma invOn_map' {c : G} (hc : InvOn R c) : InvOn (R.map φ) (φ c) := by
  rintro _ ⟨r, hr, rfl⟩
  have := congrArg φ (hc r hr)
  simpa only [map_mul, map_inv] using this

lemma agreeOn_map' {x y : G} (h : AgreeOn R x y) : AgreeOn (R.map φ) (φ x) (φ y) := by
  rintro _ ⟨r, hr, rfl⟩
  have := congrArg φ (h r hr)
  simpa only [map_mul, map_inv] using this

theorem isGL23Data_map {i j h t : G} (hd : IsGL23Data R i j h t) :
    IsGL23Data (R.map φ) (φ i) (φ j) (φ h) (φ t) := by
  have hN : ∀ {g : G}, g ∈ Subgroup.normalizer (R : Set G) →
      φ g ∈ Subgroup.normalizer ((R.map φ : Subgroup G') : Set G') :=
    fun {g} hg => Subgroup.le_normalizer_map φ ⟨g, hg, rfl⟩
  refine ⟨⟨hN hd.mem_i, hN hd.mem_j, hN hd.mem_h, ?_, ?_, ?_, ?_, ?_⟩, hN hd.mem_t, ?_⟩
  · simpa only [map_commutatorElement] using invOn_map' φ hd.inv_comm
  · simpa only [map_mul] using invOn_map' φ hd.inv_ii
  · simpa only [map_mul] using invOn_map' φ hd.inv_jj
  · simpa only [map_mul, map_inv] using agreeOn_map' φ hd.conj_i
  · simpa only [map_mul, map_inv] using agreeOn_map' φ hd.conj_j
  · have hlist : ∀ a' ∈ [1, φ i, φ j, φ i * φ j], ∃ a ∈ [1, i, j, i * j], a' = φ a := by
      intro a' ha'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
      rcases ha' with rfl | rfl | rfl | rfl
      · exact ⟨1, by simp, (map_one φ).symm⟩
      · exact ⟨i, by simp, rfl⟩
      · exact ⟨j, by simp, rfl⟩
      · exact ⟨i * j, by simp, (map_mul φ i j).symm⟩
    intro a' ha' b' hb'
    obtain ⟨a, ha, rfl⟩ := hlist a' ha'
    obtain ⟨b, hb, rfl⟩ := hlist b' hb'
    obtain ⟨h12, m, hm⟩ := hd.comm a ha b hb
    have hφc : ⁅(φ a)⁻¹ * φ h, (φ b)⁻¹ * φ t⁆ = φ ⁅a⁻¹ * h, b⁻¹ * t⁆ := by
      simp only [map_commutatorElement, map_mul, map_inv]
    rw [hφc]
    refine ⟨by rw [← map_pow, h12, map_one], m, ?_⟩
    simpa only [map_mul, map_inv, map_zpow] using agreeOn_map' φ hm

end GL23

section Core

open CFSG.Quasithin.B45Tor

lemma card_Hc : Nat.card Hc = 5 ^ 4 := by
  rw [Nat.card_eq_fintype_card]
  simp [Hc, Fintype.card_pi]

variable {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal]

lemma exists_sylow_center_eq (hshape : CFSG.RankThree.PartOne.K1214.SylowShape 5 2 2 K)
    (hidx : K.index = 5) (σ : Y) (hσ : orderOf σ = 5) (hσK : σ ∉ K)
    (hF : ∀ F : Subgroup Y, IsPGroup 5 F → F ≤ K → F ≤ Subgroup.centralizer ({σ} : Set Y) →
      Nat.card F ≤ 25)
    (E₀ : Subgroup Y) (hE₀K : E₀ ≤ K) (hE₀σ : E₀ ≤ Subgroup.centralizer ({σ} : Set Y))
    (hE₀ : IsElemAbelian 5 E₀) (hc : Nat.card E₀ = 5 ^ 2) :
    ∃ S₀ : Sylow 5 Y, E₀ ≤ (S₀ : Subgroup Y) ∧ centerOf (S₀ : Subgroup Y) = E₀ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [isElemAbelian_iff] at hE₀
  have hpE : IsPGroup 5 E₀ := fun x => ⟨1, Subtype.ext (by simpa using hE₀.2 x x.2)⟩
  have hpσ : IsPGroup 5 (Subgroup.zpowers σ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ]; rfl)
  have hnorm : E₀ ≤ Subgroup.normalizer ((Subgroup.zpowers σ : Subgroup Y) : Set Y) := by
    have key : ∀ g ∈ E₀, ∀ h ∈ Subgroup.zpowers σ, g * h * g⁻¹ = h := by
      intro g hg
      have hgσ : σ * g = g * σ :=
        Subgroup.mem_centralizer_iff.1 (hE₀σ hg) σ (Set.mem_singleton σ)
      have hcomm : Commute g σ := hgσ.symm
      rintro _ ⟨n, rfl⟩
      exact mul_inv_eq_iff_eq_mul.2 (hcomm.zpow_right n).eq
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; rw [key g hg h hh]; exact hh
    · intro hh
      have e := key g⁻¹ (E₀.inv_mem hg) _ hh
      rw [inv_inv] at e
      have : h = g * h * g⁻¹ := by
        calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
          _ = _ := e
      rw [this]; exact hh
  obtain ⟨S₀, hS₀⟩ := (hpE.to_sup_of_normal_right' hpσ hnorm).exists_le_sylow
  have hσS : σ ∈ (S₀ : Subgroup Y) := hS₀ (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))
  have hE₀S : E₀ ≤ (S₀ : Subgroup Y) := le_sup_left.trans hS₀
  refine ⟨S₀, hE₀S, ?_⟩
  obtain ⟨e⟩ := sylow_inf_homocyclic K hshape S₀
  have hPcard : Nat.card ↥((S₀ : Subgroup Y) ⊓ K) = 5 ^ 4 := by
    rw [Nat.card_congr e.toEquiv, card_Hc]
  exact center_eq_of_abelian_sylow K hidx σ hσ hσK S₀ hσS hPcard (comm_of_homocyclic e) hF E₀
    (le_inf hE₀S hE₀K) hE₀σ (by rw [hc]; norm_num)

lemma centralizer_eq_sylow (hidx : K.index = 5)
    (hM2K : ∀ (P : Sylow 5 K) (E : Subgroup K), E ≤ (P : Subgroup K) → IsElemAbelian 5 E →
      Nat.card E = 5 ^ 2 → Subgroup.centralizer (E : Set K) = (P : Subgroup K))
    (S : Sylow 5 Y) (E : Subgroup Y) (hES : E ≤ (S : Subgroup Y) ⊓ K) (hE : IsElemAbelian 5 E)
    (hc : Nat.card E = 5 ^ 2) (hEc : E ≤ Subgroup.centralizer ((S : Subgroup Y) : Set Y)) :
    Subgroup.centralizer (E : Set Y) = (S : Subgroup Y) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set C := Subgroup.centralizer (E : Set Y) with hC
  have hSC : (S : Subgroup Y) ≤ C := by
    intro s hs
    refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
    exact (Subgroup.mem_centralizer_iff.1 (hEc he) s hs).symm
  have hEK : E ≤ K := hES.trans inf_le_right
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_inf K S
  have hE'Q : E.subgroupOf K ≤ (Q : Subgroup K) := by
    intro x hx
    rw [hQ]
    exact Subgroup.mem_subgroupOf.2 (hES (Subgroup.mem_subgroupOf.1 hx))
  have hE'ab : IsElemAbelian 5 (E.subgroupOf K) := by
    rw [isElemAbelian_iff] at hE ⊢
    refine ⟨fun a ha b hb => Subtype.ext (hE.1 _ ha _ hb), fun x hx => Subtype.ext ?_⟩
    simpa using hE.2 _ hx
  have hE'c : Nat.card (E.subgroupOf K) = 5 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hc]
  have hcent := hM2K Q (E.subgroupOf K) hE'Q hE'ab hE'c
  have hCK : C ⊓ K ≤ (S : Subgroup Y) ⊓ K := by
    intro z hz
    obtain ⟨hzC, hzK⟩ := Subgroup.mem_inf.1 hz
    have : (⟨z, hzK⟩ : K) ∈ Subgroup.centralizer ((E.subgroupOf K : Subgroup K) : Set K) := by
      refine Subgroup.mem_centralizer_iff.2 fun x hx => Subtype.ext ?_
      exact Subgroup.mem_centralizer_iff.1 hzC _ (Subgroup.mem_subgroupOf.1 hx)
    rw [hcent, hQ] at this
    exact Subgroup.mem_subgroupOf.1 this
  have hKC : K.relIndex C ∣ 5 := hidx ▸ Subgroup.relIndex_dvd_index_of_normal K C
  have hmul := Subgroup.relIndex_mul_card (H := K) (K := C)
  have h1 : Nat.card ↥(K ⊓ C) ≤ Nat.card ↥((S : Subgroup Y) ⊓ K) :=
    Subgroup.card_le_of_le (by rw [inf_comm]; exact hCK)
  have h2 : K.relIndex C ≤ 5 := Nat.le_of_dvd (by norm_num) hKC
  have hcardC : Nat.card C ≤ Nat.card (S : Subgroup Y) := by
    rw [card_sylow_eq_mul_inf K hidx S, ← hmul]
    exact Nat.mul_le_mul h2 h1
  exact (Subgroup.eq_of_le_of_card_ge hSC hcardC).symm

lemma exists_conj_eq_plane (hshape : CFSG.RankThree.PartOne.K1214.SylowShape 5 2 2 K)
    (S₀ : Sylow 5 Y) (E₀ : Subgroup Y) (hE₀ : E₀ ≤ (S₀ : Subgroup Y) ⊓ K)
    (hE₀5 : ∀ x ∈ E₀, x ^ 5 = 1) (hE₀c : Nat.card E₀ = 5 ^ 2)
    (R : Subgroup Y) (hRK : R ≤ K) (hR5 : ∀ r ∈ R, r ^ 5 = 1) (hRc : Nat.card R = 5 ^ 2) :
    ∃ g : Y, E₀ = R.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hRp : IsPGroup 5 R := fun x => ⟨1, Subtype.ext (by simpa using hR5 x x.2)⟩
  obtain ⟨Q, hQ⟩ := hRp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S₀ Q
  obtain ⟨e⟩ := sylow_inf_homocyclic K hshape S₀
  refine ⟨g⁻¹, ?_⟩
  refine eq_of_exponent_five_of_homocyclic e hE₀ ?_ hE₀5 ?_ hE₀c ?_
  · rintro _ ⟨r, hr, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hrQ : r ∈ (Q : Subgroup Y) := hQ hr
      rw [← hg, mem_smul_sylow] at hrQ
      simpa [MulAut.conj_apply] using hrQ
    · simpa [MulAut.conj_apply] using Subgroup.Normal.conj_mem inferInstance r (hRK hr) g⁻¹
  · rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow, hR5 r hr, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hRc]
    norm_num

omit [Finite Y] in
lemma coe_smul_sylow_eq_map {p : ℕ} [Fact p.Prime] (S : Sylow p Y) (g : Y) :
    ((g • S : Sylow p Y) : Subgroup Y) = (S : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_smul_sylow, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply]; group⟩
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      simp [MulAut.conj_apply]; group
    rw [e]; exact hy

theorem reeF4_core_Y (hshape : CFSG.RankThree.PartOne.K1214.SylowShape 5 2 2 K)
    (hM2K : ∀ (P : Sylow 5 K) (E : Subgroup K), E ≤ (P : Subgroup K) → IsElemAbelian 5 E →
      Nat.card E = 5 ^ 2 → Subgroup.centralizer (E : Set K) = (P : Subgroup K))
    (hσ : K.index = 5 ∧ ∃ σ : Y, σ ∉ K ∧ orderOf σ = 5 ∧
      (∀ F : Subgroup Y, IsPGroup 5 F → F ≤ K → F ≤ Subgroup.centralizer ({σ} : Set Y) →
        Nat.card F ≤ 25) ∧
      ∃ E : Subgroup Y, E ≤ K ∧ E ≤ Subgroup.centralizer ({σ} : Set Y) ∧
        IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2)
    (hplane : ∃ (R : Subgroup Y) (i j h t : Y), R ≤ K ∧ (∀ r ∈ R, r ^ 5 = 1) ∧
      Nat.card R = 5 ^ 2 ∧ IsGL23Data R i j h t)
    (T : Sylow 5 Y) :
    centerOf (T : Subgroup Y) ≤ K ∧ IsElemAbelian 5 (centerOf (T : Subgroup Y)) ∧
      Nat.card (centerOf (T : Subgroup Y)) = 5 ^ 2 ∧
      Subgroup.centralizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) = (T : Subgroup Y) ∧
      ∃ i j h t : Y, IsGL23Data (centerOf (T : Subgroup Y)) i j h t := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hidx, σ, hσK, hσo, hF, E₀, hE₀K, hE₀σ, hE₀, hc⟩ := hσ
  obtain ⟨S₀, hE₀S, hcen⟩ :=
    exists_sylow_center_eq K hshape hidx σ hσo hσK hF E₀ hE₀K hE₀σ hE₀ hc
  have hE₀SK : E₀ ≤ (S₀ : Subgroup Y) ⊓ K := le_inf hE₀S hE₀K
  have hcent : Subgroup.centralizer (E₀ : Set Y) = (S₀ : Subgroup Y) :=
    centralizer_eq_sylow K hidx hM2K S₀ E₀ hE₀SK hE₀ hc (by rw [← hcen]; exact inf_le_right)
  obtain ⟨R, i, j, h, t, hRK, hR5, hRc, hd⟩ := hplane
  obtain ⟨g₁, hg₁⟩ := exists_conj_eq_plane K hshape S₀ E₀ hE₀SK ((isElemAbelian_iff _).1 hE₀).2
    hc R hRK hR5 hRc
  have hGL : IsGL23Data E₀ ((MulAut.conj g₁).toMonoidHom i) ((MulAut.conj g₁).toMonoidHom j)
      ((MulAut.conj g₁).toMonoidHom h) ((MulAut.conj g₁).toMonoidHom t) := by
    rw [hg₁]; exact isGL23Data_map _ hd
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S₀ T
  have hT : (T : Subgroup Y) = (S₀ : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]; exact coe_smul_sylow_eq_map S₀ g
  rw [hT, centerOf_map_conj, hcen]
  refine ⟨?_, isElemAbelian_map' _ hE₀, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using Subgroup.Normal.conj_mem inferInstance x (hE₀K hx) g
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc]
  · rw [centralizer_map_conj, hcent]
  · exact ⟨_, _, _, _, isGL23Data_map (MulAut.conj g).toMonoidHom hGL⟩


end Core

section Transport

lemma transport_centralizer_sylow {K' Γ : Type*} [Group K'] [Group Γ] [Finite K'] (e : K' ≃* Γ)
    (hM2 : ∀ (P : Sylow 5 Γ) (E : Subgroup Γ), E ≤ (P : Subgroup Γ) → IsElemAbelian 5 E →
      Nat.card E = 5 ^ 2 → Subgroup.centralizer (E : Set Γ) = (P : Subgroup Γ)) :
    ∀ (P : Sylow 5 K') (E : Subgroup K'), E ≤ (P : Subgroup K') → IsElemAbelian 5 E →
      Nat.card E = 5 ^ 2 → Subgroup.centralizer (E : Set K') = (P : Subgroup K') := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro P E hEP hE hc
  let P' : Sylow 5 Γ := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP' : (P' : Subgroup Γ) = (P : Subgroup K').map e.toMonoidHom := rfl
  have h := hM2 P' (E.map e.toMonoidHom) (hP' ▸ Subgroup.map_mono hEP)
    (isElemAbelian_map' _ hE) (by rw [Subgroup.card_map_of_injective e.injective, hc])
  ext x
  have hx : x ∈ Subgroup.centralizer (E : Set K') ↔
      e x ∈ Subgroup.centralizer ((E.map e.toMonoidHom : Subgroup Γ) : Set Γ) := by
    simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · rintro hx _ ⟨y, hy, rfl⟩
      simpa using congrArg e (hx y hy)
    · intro hx y hy
      have := hx (e y) ⟨y, hy, rfl⟩
      exact e.injective (by simpa using this)
  rw [hx, h, hP']
  simp

end Transport

section Main

open CFSG.Quasithin.B45Tor CFSG.LieType.Ree.ReeTag
open CFSG.AGLEmbedding (CatGroup)


set_option linter.unusedVariables false in
theorem reeF4_local_core
    {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal] (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.AGLEmbedding.IsReeFFourFiveIndex d) (e : Nonempty (K ≃* CatGroup d))
    (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (hσ : K.index = 5 ∧ ∃ σ : Y, σ ∉ K ∧ orderOf σ = 5 ∧
      (∀ F : Subgroup Y, IsPGroup 5 F → F ≤ K → F ≤ Subgroup.centralizer ({σ} : Set Y) →
        Nat.card F ≤ 25) ∧
      ∃ E : Subgroup Y, E ≤ K ∧ E ≤ Subgroup.centralizer ({σ} : Set Y) ∧
        CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2)
    (hM2 : ∀ (F : Type) [Field F] [Finite F] [CharP F CFSG.LieType.Ree.ReeTag.F4.prime],
      Nat.card F = 2 ^ (2 * 2 + 1) →
      ∀ (P : Sylow 5 (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2))
        (E : Subgroup (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2)), E ≤ (P : Subgroup _) →
        CFSG.Open.IsElemAbelian 5 E → Nat.card E = 5 ^ 2 →
        Subgroup.centralizer (E : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2)) = (P : Subgroup _))
    (T : Sylow 5 Y) :
    centerOf (T : Subgroup Y) ≤ K ∧ CFSG.Open.IsElemAbelian 5 (centerOf (T : Subgroup Y)) ∧
      Nat.card (centerOf (T : Subgroup Y)) = 5 ^ 2 ∧
      Subgroup.centralizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) = (T : Subgroup Y) ∧
      ∃ i j h t : Y, CFSG.Quasithin.B45Tor.IsGL23Data (centerOf (T : Subgroup Y)) i j h t := by
  have hmodel := CFSG.AGLEmbedding.reeTitsModel_of_catGroup_reeF4 hd
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier (CatGroup d) 2 (2 * 2 + 1) hmodel
  obtain ⟨-, a, hfa, F, _, _, hF, ⟨e'⟩⟩ := hmodel
  have hFc : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have : CharP F F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hF
  obtain ⟨eΓ⟩ := hS.2.2.2.2.2 a F hfa hF ⟨e'⟩
  have ha : a = 2 := by omega
  subst ha
  obtain ⟨eK0⟩ := e
  let eK : K ≃* F4.reeGamma F 2 := eK0.trans eΓ
  have hshapeΓ : CFSG.RankThree.PartOne.K1214.SylowShape 5 2 2 (F4.reeGamma F 2) := by
    have h := CFSG.RankThree.PartOne.K128.sylowShape_ree_phi4 (a := 2) (K := F) hFc
      Nat.prime_five le_rfl (by norm_num)
    have hv : (((2 ^ (2 * 2 + 1)) ^ 2 + 1).factorization 5) = 2 := by
      have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      rw [Nat.factorization_def _ Nat.prime_five]
      have h25 : (2 ^ (2 * 2 + 1)) ^ 2 + 1 = 5 ^ 2 * 41 := by norm_num
      rw [h25, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rwa [hv] at h
  have hshape : CFSG.RankThree.PartOne.K1214.SylowShape 5 2 2 K :=
    CFSG.RankThree.PartOne.K1214.SylowShape.of_mulEquiv eK hshapeΓ
  have hM2K := transport_centralizer_sylow eK (hM2 F hFc)
  obtain ⟨R, i, j, h, t, -, hR5, hRc, hGL, -, -⟩ :=
    CFSG.Quasithin.B45Tor.exists_reePlane (K := F) (a := 2) (by norm_num) hFc
      (p := 5) Nat.prime_five (by norm_num) (Or.inl (by norm_num))
  let φ₀ : F4.reeGamma F 2 →* Y := K.subtype.comp eK.symm.toMonoidHom
  have hφ₀ : Function.Injective φ₀ := Subtype.val_injective.comp eK.symm.injective
  refine reeF4_core_Y K hshape hM2K hσ ⟨R.map φ₀, φ₀ i, φ₀ j, φ₀ h, φ₀ t, ?_, ?_, ?_,
    isGL23Data_map φ₀ hGL⟩ T
  · rintro _ ⟨r, -, rfl⟩
    exact (eK.symm r).2
  · rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow, hR5 r hr, map_one]
  · rw [Subgroup.card_map_of_injective hφ₀, hRc]

end Main


end CFSG.HardMathSupport.Malle.LocalAction
