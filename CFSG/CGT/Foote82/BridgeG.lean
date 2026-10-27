module

public import CFSG.CGT.Foote82.TildeULin
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.CoprimeFixedPoint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace BridgeG

private theorem not_le_center_of_isQuasisimple {P : Type*} [Group P] {K : Subgroup P}
    (hK : CFSG.Open.IsQuasisimple ↥K) : ¬ K ≤ Subgroup.center P := by
  intro hle
  have hc : ∀ x : ↥K, x ∈ Subgroup.center ↥K := fun x => by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hle x.2) y)
  haveI := hK.2.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥K ⧸ Subgroup.center ↥K)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by
    rw [(QuotientGroup.eq_one_iff a).mpr (hc a), (QuotientGroup.eq_one_iff b).mpr (hc b)])

private theorem isQuasisimple_native {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩

private theorem isQuasisimple_open {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem layer_eq_of_normal_quasisimple {Y : Type*} [Group Y] (E : Subgroup Y) [E.Normal]
    (hE : CFSG.IsQuasisimple ↥E) (hsolv : Group.IsSolvable (Y ⧸ E)) : CFSG.layer Y = E := by
  refine le_antisymm (sSup_le fun K hK => ?_)
    (le_sSup ⟨hE, Subgroup.Normal.isSubnormal inferInstance⟩)
  have hperf : Group.IsPerfect ↥K := hK.1.1
  let f : ↥K →* Y ⧸ E := (QuotientGroup.mk' E).comp K.subtype
  have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  intro x hx
  by_contra hxE
  have hnt : Nontrivial ↥f.range := by
    refine ⟨⟨⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, 1, fun h => hxE ?_⟩⟩
    have h1 : f ⟨x, hx⟩ = 1 := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff x).mp h1
  exact Group.IsPerfect.not_isSolvable ↥f.range inferInstance

private theorem normalClosure_conj_mem {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Γ L : Subgroup (GLV V)} {γ x : GLV V} (hγ : γ ∈ Γ) (hx : x ∈ normalClosure Γ L) :
    γ * x * γ⁻¹ ∈ normalClosure Γ L := by
  unfold normalClosure at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨γ', hγ', l, hl, rfl⟩ := hy
    exact Subgroup.subset_closure ⟨γ * γ', Γ.mul_mem hγ hγ', l, hl, by group⟩
  | one => simp
  | mul y z _ _ hy hz =>
    have : γ * (y * z) * γ⁻¹ = (γ * y * γ⁻¹) * (γ * z * γ⁻¹) := by group
    rw [this]; exact mul_mem hy hz
  | inv y _ hy =>
    have : γ * y⁻¹ * γ⁻¹ = (γ * y * γ⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hy

private theorem le_normalClosure {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Γ L : Subgroup (GLV V)) : L ≤ normalClosure Γ L := fun l hl =>
  Subgroup.subset_closure ⟨1, Γ.one_mem, l, hl, by simp⟩

private theorem normalClosure_le {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Γ L : Subgroup (GLV V)} (h : L ≤ Γ) : normalClosure Γ L ≤ Γ := by
  unfold normalClosure
  rw [Subgroup.closure_le]
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  exact Γ.mul_mem (Γ.mul_mem hγ (h hl)) (Γ.inv_mem hγ)

private theorem isIrr_top_mono {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {K K' : Subgroup (GLV V)} (h : IsIrr K ⊤) (hK : K ≤ K') : IsIrr K' ⊤ := by
  obtain ⟨-, hlt, hirr⟩ := h
  exact ⟨fun _ _ _ _ => Submodule.mem_top, hlt,
    fun J hJ h1 h2 => hirr J (fun k hk u hu => hJ k (hK hk) u hu) h1 h2⟩

private theorem conj_mem_pCoreOf {J : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (J : Set G))
    {q : G} (hq : q ∈ pCoreOf 2 J) : t * q * t⁻¹ ∈ pCoreOf 2 J := by
  obtain ⟨q', hq', rfl⟩ := hq
  have h := CFSG.pCore_map_iso 2 (J.normalizerMonoidHom ⟨t, ht⟩)
  have : (J.normalizerMonoidHom ⟨t, ht⟩) q' ∈ CFSG.pCore 2 ↥J := by
    rw [← h]; exact Subgroup.mem_map_of_mem _ hq'
  exact ⟨_, this, rfl⟩

private def centMod (J₂ T : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ J₂ ∧ ∀ t ∈ T, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 J₂}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨J₂.mul_mem ha hb, fun t ht => ?_⟩
    have h1 := (pCoreOf 2 J₂).mul_mem (ha' t ht)
      (conj_mem_pCoreOf (J := J₂) (Subgroup.le_normalizer ha) (hb' t ht))
    have h2 : t * (a * b) * t⁻¹ * (a * b)⁻¹ =
        t * a * t⁻¹ * a⁻¹ * (a * (t * b * t⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [h2]
    exact h1
  one_mem' := ⟨J₂.one_mem, fun t _ => by simpa using (pCoreOf 2 J₂).one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨J₂.inv_mem ha, fun t ht => ?_⟩
    have h1 := conj_mem_pCoreOf (J := J₂) (Subgroup.le_normalizer (J₂.inv_mem ha))
      ((pCoreOf 2 J₂).inv_mem (ha' t ht))
    have h2 : t * a⁻¹ * t⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (t * a * t⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ := by group
    rw [h2]
    exact h1

private theorem centMod_le (J₂ T : Subgroup G) : centMod J₂ T ≤ J₂ := fun _ hx => hx.1

private theorem pCoreOf_le_centMod {J₂ T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (J₂ : Set G)) : pCoreOf 2 J₂ ≤ centMod J₂ T := fun q hq =>
  ⟨Subgroup.map_subtype_le _ hq, fun t ht =>
    (pCoreOf 2 J₂).mul_mem (conj_mem_pCoreOf (hTN ht) hq) ((pCoreOf 2 J₂).inv_mem hq)⟩

private theorem centralizerBarIn_eq (J₂ T : Subgroup G) :
    centralizerBarIn J₂ T = barIn J₂ (centMod J₂ T) := by
  unfold centralizerBarIn
  rw [show Subgroup.closure {x : G | x ∈ J₂ ∧ ∀ t ∈ T, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 J₂} =
    centMod J₂ T from Subgroup.closure_eq (centMod J₂ T)]

private theorem le_centMod_of_barIn_le {J₁ J₂ T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (J₂ : Set G)) (hJ₁J₂ : J₁ ≤ J₂)
    (hle : barIn J₂ J₁ ≤ centralizerBarIn J₂ T) : J₁ ≤ centMod J₂ T := by
  intro x hx
  have hxb : (QuotientGroup.mk ⟨x, hJ₁J₂ hx⟩ : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂) ∈ barIn J₂ J₁ :=
    ⟨⟨x, hJ₁J₂ hx⟩, hx, rfl⟩
  rw [centralizerBarIn_eq] at hle
  obtain ⟨z, hz, hzx⟩ := hle hxb
  have h1 : z⁻¹ * ⟨x, hJ₁J₂ hx⟩ ∈ CFSG.pCore 2 ↥J₂ := QuotientGroup.eq.mp hzx
  have h3 : x = (z : G) * ((z⁻¹ * ⟨x, hJ₁J₂ hx⟩ : ↥J₂) : G) := by simp
  rw [h3]
  exact (centMod J₂ T).mul_mem hz (pCoreOf_le_centMod hTN ⟨_, h1, rfl⟩)

private theorem normalClosure_eq_top {J₁ J₂ : Subgroup G} (h2 : IsFooteBlock J₂ J₂)
    (hq : CFSG.Open.IsQuasisimple ↥(barIn J₂ J₁)) :
    Subgroup.normalClosure ((J₁.subgroupOf J₂ : Subgroup ↥J₂) : Set ↥J₂) = ⊤ := by
  set N : Subgroup ↥J₂ := Subgroup.normalClosure ((J₁.subgroupOf J₂ : Subgroup ↥J₂) : Set ↥J₂)
    with hN
  set Q := CFSG.pCore 2 ↥J₂ with hQ
  haveI hNb : (N.map (QuotientGroup.mk' Q)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Q)
  have hbar_le : barIn J₂ J₁ ≤ N.map (QuotientGroup.mk' Q) :=
    Subgroup.map_mono (Subgroup.subset_normalClosure)
  have hNQ : N ⊔ Q = ⊤ := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top h2.quasisimple
      (N.map (QuotientGroup.mk' Q)) with hc | htop
    · exact absurd (hbar_le.trans hc) (not_le_center_of_isQuasisimple hq)
    · have := Subgroup.comap_map_eq (QuotientGroup.mk' Q) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
  have hpg : IsPGroup 2 (↥J₂ ⧸ N) := by
    refine (CFSG.pCore_isPGroup (p := 2) (G := ↥J₂)).of_surjective
      ((QuotientGroup.mk' N).comp Q.subtype) ?_
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : z ∈ N ⊔ Q := hNQ ▸ Subgroup.mem_top z
    obtain ⟨n, hn, q, hq', rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hz
    refine ⟨⟨q, hq'⟩, ?_⟩
    change QuotientGroup.mk q = QuotientGroup.mk (n * q)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  exact h2.residual N hpg

end BridgeG

namespace BridgeG

variable {J₁ J₂ T : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (lin : TildeULin J₂ (J₂ ⊔ T) V)

private noncomputable def conjAct (hTN : T ≤ Subgroup.normalizer (J₂ : Set G)) :
    ↥T →* MulAut ↥J₂ :=
  J₂.normalizerMonoidHom.comp (Subgroup.inclusion hTN)

private theorem conjAct_pCore (hTN : T ≤ Subgroup.normalizer (J₂ : Set G)) (t : ↥T) {n : ↥J₂}
    (hn : n ∈ CFSG.pCore 2 ↥J₂) : conjAct hTN t n ∈ CFSG.pCore 2 ↥J₂ := by
  have h := CFSG.pCore_map_iso 2 (conjAct hTN t)
  rw [← h]; exact Subgroup.mem_map_of_mem _ hn

private noncomputable def barAct (hTN : T ≤ Subgroup.normalizer (J₂ : Set G)) :
    ↥T →* MulAut (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) :=
  quotientAction (conjAct hTN) (CFSG.pCore 2 ↥J₂) (fun t _ hn => conjAct_pCore hTN t hn)

private theorem barAct_mk (hTN : T ≤ Subgroup.normalizer (J₂ : Set G)) (t : ↥T) (j : ↥J₂) :
    barAct hTN t (QuotientGroup.mk j) = QuotientGroup.mk (conjAct hTN t j) := rfl

private theorem ρbar_barAct (h2 : IsFooteBlock J₂ J₂) (hTN : T ≤ Subgroup.normalizer (J₂ : Set G))
    (t : ↥T) (x : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂) :
    lin.ρbar h2 le_sup_left (barAct hTN t x) =
      lin.ρ (Subgroup.inclusion (le_sup_right : T ≤ J₂ ⊔ T) t) * lin.ρbar h2 le_sup_left x *
        (lin.ρ (Subgroup.inclusion (le_sup_right : T ≤ J₂ ⊔ T) t))⁻¹ := by
  induction x using QuotientGroup.induction_on with
  | H j =>
    rw [barAct_mk, lin.ρbar_mk, lin.ρbar_mk, ← map_inv, ← map_mul, ← map_mul]
    rfl

end BridgeG

namespace TildeULin

variable {J₁ J₂ T : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (lin : TildeULin J₂ (J₂ ⊔ T) V)

theorem exists_preimage_centralizer (h2 : IsFooteBlock J₂ J₂) (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (J₂ : Set G)) (g : GLV V) (hg : g ∈ lin.img J₂)
    (hgT : g ∈ Subgroup.centralizer (lin.img T : Set (GLV V))) :
    ∃ j : ↥(J₂ ⊔ T), (j : G) ∈ J₂ ∧ lin.ρ j = g ∧
      ∀ t ∈ T, t * (j : G) * t⁻¹ * (j : G)⁻¹ ∈ blockQ J₂ := by
  have hJX : J₂ ≤ J₂ ⊔ T := le_sup_left
  obtain ⟨x, hx, rfl⟩ := hg
  set j₀ : ↥J₂ := ⟨(x : G), hx⟩ with hj₀
  have hxj₀ : x = Subgroup.inclusion hJX j₀ := rfl
  set N := (lin.ρbar h2 hJX).ker with hN
  have hcop : ¬ 2 ∣ Nat.card N := (lin.odd_card_ker_ρbar h2 hJX).not_two_dvd_nat
  have hmem : ∀ y : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂,
      (QuotientGroup.mk j₀ : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂)⁻¹ * y ∈ N ↔
        lin.ρbar h2 hJX y = lin.ρ x := by
    intro y
    rw [hN, MonoidHom.mem_ker, map_mul, map_inv, lin.ρbar_mk, ← hxj₀, inv_mul_eq_one, eq_comm]
  have hinv : ∀ (a : ↥T) (y : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂),
      (QuotientGroup.mk j₀ : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂)⁻¹ * y ∈ N →
        (QuotientGroup.mk j₀ : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂)⁻¹ * BridgeG.barAct hTN a y ∈ N := by
    intro a y hy
    rw [hmem] at hy ⊢
    rw [BridgeG.ρbar_barAct lin h2 hTN a y, hy]
    have hcomm := Subgroup.mem_centralizer_iff.mp hgT
      (lin.ρ (Subgroup.inclusion (le_sup_right : T ≤ J₂ ⊔ T) a))
      ⟨Subgroup.inclusion (le_sup_right : T ≤ J₂ ⊔ T) a, a.2, rfl⟩
    rw [hcomm, mul_inv_cancel_right]
  obtain ⟨c, hcN, hcfix⟩ :=
    (coprime_invariant_coset_fixed 2 hT (BridgeG.barAct hTN) N hcop
      (QuotientGroup.mk j₀)).2 hinv
  obtain ⟨j', rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨Subgroup.inclusion hJX j', j'.2, ?_, ?_⟩
  · have := (hmem _).mp hcN
    rwa [lin.ρbar_mk] at this
  · intro t ht
    have h1 := hcfix ⟨t, ht⟩
    rw [BridgeG.barAct_mk, QuotientGroup.eq] at h1
    have hQ : BridgeG.conjAct hTN ⟨t, ht⟩ j' * j'⁻¹ ∈ CFSG.pCore 2 ↥J₂ := by
      have h3 := (CFSG.pCore_normal (p := 2) (G := ↥J₂)).conj_mem _
        (Subgroup.inv_mem _ h1) (BridgeG.conjAct hTN ⟨t, ht⟩ j')
      simpa [mul_assoc] using h3
    exact ⟨_, hQ, rfl⟩

end TildeULin

namespace BridgeG

variable {J₁ J₂ T : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (lin : TildeULin J₂ (J₂ ⊔ T) V)

private theorem img_mono {J X : Subgroup G} (lin : TildeULin J X V) {A B : Subgroup G}
    (h : A ≤ B) : lin.img A ≤ lin.img B :=
  Subgroup.map_mono (Subgroup.comap_mono h)

private theorem img_le_normalizer {J X : Subgroup G} (lin : TildeULin J X V)
    (hX : X ≤ Subgroup.normalizer (J : Set G)) :
    lin.img X ≤ Subgroup.normalizer (lin.img J : Set (GLV V)) := by
  rintro _ ⟨x, -, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨x * j * x⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hX x.2) j).mp hj
  · rintro ⟨j, hj, hjd⟩
    refine ⟨x⁻¹ * j * x, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hX x.2)) j).mp hj
      rwa [inv_inv] at h1
    · have : lin.ρ j = lin.ρ x * d * (lin.ρ x)⁻¹ := hjd
      rw [map_mul, map_mul, map_inv, this]
      group

private theorem img_eq_map_barIn (h2 : IsFooteBlock J₂ J₂) {A : Subgroup G} (hA : A ≤ J₂) :
    lin.img A = (barIn J₂ A).map (lin.ρbar h2 le_sup_left) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨QuotientGroup.mk ⟨x, hA hx⟩, ⟨⟨x, hA hx⟩, hx, rfl⟩, ?_⟩
    rw [lin.ρbar_mk]
    rfl
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨Subgroup.inclusion le_sup_left a, ha, ?_⟩
    rw [QuotientGroup.mk'_apply, lin.ρbar_mk]

private theorem img_sup : lin.img (J₂ ⊔ T) = lin.img J₂ ⊔ lin.img T := by
  unfold TildeULin.img
  rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right]

private theorem ρ_comm_of_mem_blockQ (h2 : IsFooteBlock J₂ J₂) (t x : ↥(J₂ ⊔ T))
    (h : ((t * x * t⁻¹ * x⁻¹ : ↥(J₂ ⊔ T)) : G) ∈ blockQ J₂) :
    lin.ρ t * lin.ρ x = lin.ρ x * lin.ρ t := by
  have h1 := lin.ρ_eq_one_of_mem_blockQ h2 (t * x * t⁻¹ * x⁻¹) h
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

variable [Finite V] in
private theorem map_centralizerBarIn (h2 : IsFooteBlock J₂ J₂) (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (J₂ : Set G)) :
    (centralizerBarIn J₂ T).map (lin.ρbar h2 le_sup_left) =
      lin.img J₂ ⊓ Subgroup.centralizer (lin.img T : Set (GLV V)) := by
  rw [centralizerBarIn_eq, ← img_eq_map_barIn lin h2 (centMod_le J₂ T)]
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact ρ_comm_of_mem_blockQ lin h2 t x (hx.2 t ht)
  · rintro ⟨hg, hgT⟩
    obtain ⟨j, hj, hρ, hjt⟩ := lin.exists_preimage_centralizer h2 hT hTN g hg hgT
    exact ⟨j, ⟨hj, hjt⟩, hρ⟩

end BridgeG

namespace TildeULin

variable {J₁ J₂ T : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (lin : TildeULin J₂ (J₂ ⊔ T) V)

theorem setup6Irr_img (h1 : IsFooteBlock J₁ J₁) (h2 : IsFooteBlock J₂ J₂) (hJ₁J₂ : J₁ ≤ J₂)
    (hU : blockU J₁ = ⁅blockQ J₂, J₁⁆) (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (J₂ : Set G))
    (hcomp : IsComponentOf (barIn J₂ J₁) (centralizerBarIn J₂ T)) :
    Setup6Irr (lin.img (J₂ ⊔ T)) (lin.img T) (lin.img J₁) := by
  have hJX : J₂ ≤ J₂ ⊔ T := le_sup_left
  have hXN : J₂ ⊔ T ≤ Subgroup.normalizer (J₂ : Set G) := sup_le Subgroup.le_normalizer hTN
  have hJ₁X : J₁ ≤ J₂ ⊔ T := hJ₁J₂.trans hJX
  have hcentMod : J₁ ≤ BridgeG.centMod J₂ T :=
    BridgeG.le_centMod_of_barIn_le hTN hJ₁J₂ hcomp.1
  have hcent : lin.img J₁ ≤ Subgroup.centralizer (lin.img T : Set (GLV V)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    exact BridgeG.ρ_comm_of_mem_blockQ lin h2 t x ((hcentMod hx).2 t ht)
  have hq : CFSG.Open.IsQuasisimple ↥(lin.img J₁) := by
    have hbar : CFSG.Open.IsQuasisimple ↥(barIn J₂ J₁) := hcomp.2.2
    have hker : ¬ barIn J₂ J₁ ≤ (lin.ρbar h2 hJX).ker := fun hle =>
      BridgeG.not_le_center_of_isQuasisimple hbar
        (hle.trans (lin.ker_ρbar_le_center h2 hJX))
    have := CFSG.LocalCores.isQuasisimple_map (BridgeG.isQuasisimple_native hbar)
      (lin.ρbar h2 hJX) hker
    rw [← BridgeG.img_eq_map_barIn lin h2 hJ₁J₂] at this
    exact BridgeG.isQuasisimple_open this
  have hsub : IsSubnormal (lin.img J₁)
      (lin.img (J₂ ⊔ T) ⊓ Subgroup.centralizer (lin.img T : Set (GLV V))) := by
    have h := hcomp.2.1.map (lin.ρbar h2 hJX)
    rw [← BridgeG.img_eq_map_barIn lin h2 hJ₁J₂, BridgeG.map_centralizerBarIn lin h2 hT hTN] at h
    have hle : lin.img J₂ ⊓ Subgroup.centralizer (lin.img T : Set (GLV V)) ≤
        lin.img (J₂ ⊔ T) ⊓ Subgroup.centralizer (lin.img T : Set (GLV V)) :=
      inf_le_inf_right _ (BridgeG.img_mono lin hJX)
    refine h.trans (.step hle ?_ (.refl _))
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro d k hd hk
    exact ⟨(Subgroup.mem_normalizer_iff.mp (BridgeG.img_le_normalizer lin hXN hk.1) d).mp hd.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk.2 hd.2) (Subgroup.inv_mem _ hk.2)⟩
  refine
    { S_le := BridgeG.img_mono lin le_sup_right
      isPGroup := ?_
      component := ⟨le_inf (BridgeG.img_mono lin hJ₁X) hcent, hsub, hq⟩
      irrTilde := lin.hasIrrTildeV_img h2 h1 hJ₁X hJ₁J₂ hU
      irr := BridgeG.isIrr_top_mono (lin.isIrr_img h2 hJX) (BridgeG.img_mono lin hJX)
      gen := ?_ }
  · exact (hT.comap_of_injective (J₂ ⊔ T).subtype Subtype.val_injective).map lin.ρ
  · have hN := BridgeG.normalClosure_eq_top (J₁ := J₁) h2 hcomp.2.2
    refine le_antisymm
      ((BridgeG.img_sup lin).le.trans (sup_le (le_trans ?_ le_sup_left) le_sup_right)) ?_
    · rintro _ ⟨x, hx, rfl⟩
      set M := normalClosure (lin.img (J₂ ⊔ T)) (lin.img J₁) with hM
      let f : ↥J₂ →* GLV V := lin.ρ.comp (Subgroup.inclusion hJX)
      haveI : (M.comap f).Normal := ⟨fun n hn a => by
        change f (a * n * a⁻¹) ∈ M
        rw [map_mul, map_mul, map_inv]
        exact BridgeG.normalClosure_conj_mem ⟨Subgroup.inclusion hJX a, hJX a.2, rfl⟩ hn⟩
      have hsub : Subgroup.normalClosure ((J₁.subgroupOf J₂ : Subgroup ↥J₂) : Set ↥J₂) ≤
          M.comap f :=
        Subgroup.normalClosure_le_normal fun a ha =>
          BridgeG.le_normalClosure _ _ ⟨Subgroup.inclusion hJX a, ha, rfl⟩
      exact hsub (hN ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥J₂))
    · exact sup_le (BridgeG.normalClosure_le (BridgeG.img_mono lin hJ₁X))
        (BridgeG.img_mono lin le_sup_right)

theorem layerIn_img (h2 : IsFooteBlock J₂ J₂) (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (J₂ : Set G)) :
    layerIn (lin.img (J₂ ⊔ T)) = lin.img J₂ := by
  have hJX : J₂ ≤ J₂ ⊔ T := le_sup_left
  have hXN : J₂ ⊔ T ≤ Subgroup.normalizer (J₂ : Set G) := sup_le Subgroup.le_normalizer hTN
  set Gm := lin.img (J₂ ⊔ T) with hGm
  set E := lin.img J₂ with hE
  set S := lin.img T with hS
  have hEG : E ≤ Gm := BridgeG.img_mono lin hJX
  have hnorm : (E.subgroupOf Gm).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hEG]
    intro d k hd hk
    exact (Subgroup.mem_normalizer_iff.mp (BridgeG.img_le_normalizer lin hXN hk) d).mp hd
  have hq : CFSG.IsQuasisimple ↥(E.subgroupOf Gm) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEG).symm
      (BridgeG.isQuasisimple_native (lin.isQuasisimple_img h2 hJX))
  have hSp : IsPGroup 2 ↥S :=
    (hT.comap_of_injective (J₂ ⊔ T).subtype Subtype.val_injective).map lin.ρ
  haveI : Finite (GLV V) :=
    Finite.of_injective (fun f : GLV V => (f : V → V)) DFunLike.coe_injective
  haveI : Finite ↥Gm := inferInstance
  have hsolv : Group.IsSolvable (↥Gm ⧸ E.subgroupOf Gm) := by
    have hSp' : IsPGroup 2 ↥(S.subgroupOf Gm) :=
      hSp.comap_of_injective Gm.subtype Subtype.val_injective
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' (E.subgroupOf Gm)).comp (S.subgroupOf Gm).subtype) := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
      have hz : z ∈ E.subgroupOf Gm ⊔ S.subgroupOf Gm := by
        rw [← Subgroup.subgroupOf_sup hEG (BridgeG.img_mono lin le_sup_right),
          ← BridgeG.img_sup lin]
        exact z.2
      obtain ⟨e, he, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hz
      refine ⟨⟨s, hs⟩, ?_⟩
      change QuotientGroup.mk s = QuotientGroup.mk (e * s)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff e).mpr he, one_mul]
    haveI := (hSp'.of_surjective _ hsurj).isNilpotent
    infer_instance
  have hlayer : CFSG.layer ↥Gm = E.subgroupOf Gm :=
    BridgeG.layer_eq_of_normal_quasisimple _ hq hsolv
  change (CFSG.layer ↥Gm).map Gm.subtype = E
  rw [hlayer, Subgroup.map_subgroupOf_eq_of_le hEG]

end TildeULin

end CFSG.CGT.Foote82
