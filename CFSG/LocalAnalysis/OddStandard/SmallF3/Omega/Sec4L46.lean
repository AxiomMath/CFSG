module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4AData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4_isElemAbelian_conjugate {A : Subgroup G} (h : CFSG.Open.IsElemAbelian 2 A) (g : G) :
    CFSG.Open.IsElemAbelian 2 (CFSG.conjugate A g) := by
  haveI : IsMulCommutative ↥A := h.1
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
  · have h1 : g * (a : G) * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) :=
      congrArg Subtype.val (mul_comm' (⟨g * a * g⁻¹, (mem_conjugate_iff A g a).mp a.2⟩ : ↥A)
        ⟨g * b * g⁻¹, (mem_conjugate_iff A g b).mp b.2⟩)
    calc (a : G) * b = g⁻¹ * (g * a * g⁻¹ * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹ * (g * a * g⁻¹)) * g := by rw [h1]
      _ = (b : G) * a := by group
  · have h1 := h.2 (g * x * g⁻¹) ((mem_conjugate_iff A g x).mp hx)
    have h2 : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
    rw [h2] at h1
    calc x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

theorem sec4_isMaxElemAbelianIn_conjugate {R A : Subgroup G} (h : IsMaxElemAbelianIn R A) (g : G)
    (hg : CFSG.conjugate A g ≤ R) : IsMaxElemAbelianIn R (CFSG.conjugate A g) := by
  have hcard : Nat.card (CFSG.conjugate A g) = Nat.card A :=
    (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).toEquiv).symm
  refine ⟨hg, sec4_isElemAbelian_conjugate h.2.1 g, ?_⟩
  intro B hB hBe
  rw [hcard]
  exact h.2.2 B hB hBe

private theorem conjClassIn_conj_iff (z g y : G) :
    (MulAut.conj g⁻¹).toMonoidHom y ∈ conjClassIn ⊤ z ↔ y ∈ conjClassIn ⊤ z := by
  constructor
  · rintro ⟨h, -, hh⟩
    refine ⟨g * h, trivial, ?_⟩
    have hy : y = g * (h * z * h⁻¹) * g⁻¹ := by
      rw [← hh]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [hy]
    group
  · rintro ⟨h, -, rfl⟩
    exact ⟨g⁻¹ * h, trivial, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc]
      group⟩

theorem sec4_closure_conj_inter (z : G) (A : Subgroup G) (g : G) :
    Subgroup.closure (conjClassIn ⊤ z ∩ (CFSG.conjugate A g : Set G)) =
      CFSG.conjugate (Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G))) g := by
  let f : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hset : f '' (conjClassIn ⊤ z ∩ (A : Set G)) =
      conjClassIn ⊤ z ∩ (A.map f : Set G) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyz, hyA⟩, rfl⟩
      exact ⟨(conjClassIn_conj_iff z g y).mpr hyz, ⟨y, hyA, rfl⟩⟩
    · rintro ⟨hxz, ⟨y, hyA, rfl⟩⟩
      exact ⟨y, ⟨(conjClassIn_conj_iff z g y).mp hxz, hyA⟩, rfl⟩
  have hmap : Subgroup.closure (conjClassIn ⊤ z ∩ (A.map f : Set G)) =
      (Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G))).map f := by
    rw [← hset, MonoidHom.map_closure]
  simpa [CFSG.conjugate, f] using hmap

theorem sec4_zG_cap_C_le [Finite G] (h43 : Asc82Lemma43) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec4Ctx G t L S z) {w : G} (hw : w ∈ conjClassIn ⊤ z)
    (hwt : w ∈ centralizer ({t} : Set G)) : w ∈ L ⊔ centralizer (L : Set G) := by
  have hzL : z ∈ L := hctx.pocket.mem
  have htC : t ∈ centralizer (L : Set G) :=
    sec4_t_mem_centralizer hctx.toSec4Setting.toSec3SettingLB.toSec3Setting
  obtain ⟨h, -, hh⟩ := hw
  have hg : (h⁻¹)⁻¹ * z * h⁻¹ = w := by rw [inv_inv, hh]
  have hcase := h43 G t L S z hctx h⁻¹ (by rw [hg]; exact hwt)
  rw [hg] at hcase
  rcases hcase with hwz | hwtz
  · obtain ⟨l, hl, hlw⟩ := hwz
    rw [hlw]
    exact Subgroup.mem_sup_left (L.mul_mem (L.mul_mem hl hzL) (L.inv_mem hl))
  · obtain ⟨l, hl, hlw⟩ := hwtz
    rw [hlw]
    have hlt : l * t = t * l := Subgroup.mem_centralizer_iff.mp htC l hl
    have hctc : l * (t * z) * l⁻¹ = t * (l * z * l⁻¹) := by
      calc l * (t * z) * l⁻¹ = (l * t) * z * l⁻¹ := by group
        _ = (t * l) * z * l⁻¹ := by rw [hlt]
        _ = t * (l * z * l⁻¹) := by group
    rw [hctc, sup_comm]
    exact Subgroup.mul_mem_sup htC (L.mul_mem (L.mul_mem hl hzL) (L.inv_mem hl))

theorem sec4_weakly_closed [Finite G] (h43 : Asc82Lemma43) (h46a : Asc82Lemma46a) {t : G}
    {L S : Subgroup G} {z : G} {A B : Subgroup G} {φ : (Fin 7 → ZMod 2) → G}
    (hctx : Sec4Ctx G t L S z) (hD : Sec4AData t L S z A B φ) {g : G}
    (hg : CFSG.conjugate A g ≤ S) : CFSG.conjugate A g = A := by
  have hS : S ≤ centralizer ({t} : Set G) := hctx.sylow.1
  have hzL : z ∈ L := hctx.pocket.mem
  have hBA : B ≤ A := hD.B_eq ▸ inf_le_left
  have hsubset : (conjClassIn ⊤ z ∩ (CFSG.conjugate A g : Set G)) ⊆ SLC S L :=
    fun w ⟨hwz, hwg⟩ => ⟨hg hwg, sec4_zG_cap_C_le h43 hctx hwz (hS (hg hwg))⟩
  rcases h46a G t L S z hctx A hD.isMax with ⟨⟨_, _⟩, hAcl⟩ | ⟨hCeq, hAcl⟩
  · have hcl : Subgroup.closure (conjClassIn ⊤ z ∩ (CFSG.conjugate A g : Set G)) =
        CFSG.conjugate A g := by
      rw [sec4_closure_conj_inter z A g, ← hAcl]
    have hle : CFSG.conjugate A g ≤ SLC S L := by
      rw [← hcl]
      exact (Subgroup.closure_le _).mpr hsubset
    exact hD.unique _ (sec4_isMaxElemAbelianIn_conjugate hD.isMax g hle)
  · have hB : B = Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G)) := by
      rw [← hD.B_eq, hAcl]
    have hcl : Subgroup.closure (conjClassIn ⊤ z ∩ (CFSG.conjugate A g : Set G)) =
        CFSG.conjugate B g := by
      rw [sec4_closure_conj_inter z A g, ← hB]
    have hBg_le : CFSG.conjugate B g ≤ S ⊓ L := by
      rw [← hcl]
      refine (Subgroup.closure_le _).mpr ?_
      rintro w ⟨hwz, hwg⟩
      have hwS : w ∈ S := hg hwg
      have hwzL : w ∈ conjClassIn L z := by
        have hmem : w ∈ conjClassIn ⊤ z ∩ (centralizer ({t} : Set G) : Set G) :=
          ⟨hwz, hS hwS⟩
        rwa [hCeq] at hmem
      obtain ⟨l, hl, rfl⟩ := hwzL
      exact ⟨hwS, L.mul_mem (L.mul_mem hl hzL) (L.inv_mem hl)⟩
    have hBg : CFSG.conjugate B g = B :=
      hD.bdata.unique _ (sec4_isMaxElemAbelianIn_conjugate hD.bdata.isMax g hBg_le)
    have hBg' : B.map (MulAut.conj g⁻¹).toMonoidHom = B := hBg
    have hft : (MulAut.conj g⁻¹).toMonoidHom t = g⁻¹ * t * g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hAg_eq : CFSG.conjugate A g = B ⊔ Subgroup.zpowers (g⁻¹ * t * g) := by
      rw [hD.A_eq, CFSG.conjugate, Subgroup.map_sup, hBg', MonoidHom.map_zpowers, hft]
    have htA : t ∈ A := by
      rw [hD.A_eq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have htgA : g⁻¹ * t * g ∈ CFSG.conjugate A g := by
      rw [mem_conjugate_iff]
      rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
    have htgm : g⁻¹ * t * g ∈ SLC S L := by
      refine hD.centB _ (hg htgA) ?_
      intro b hb
      have hbBg : b ∈ CFSG.conjugate B g := by rw [hBg]; exact hb
      have hbA : b ∈ CFSG.conjugate A g := Subgroup.map_mono hBA hbBg
      haveI : IsMulCommutative ↥(CFSG.conjugate A g) :=
        (sec4_isElemAbelian_conjugate hD.isMax.2.1 g).1
      exact congrArg Subtype.val (mul_comm'
        (⟨g⁻¹ * t * g, htgA⟩ : ↥(CFSG.conjugate A g)) ⟨b, hbA⟩)
    have hle : CFSG.conjugate A g ≤ SLC S L := by
      rw [hAg_eq]
      refine sup_le ?_ ?_
      · rw [← hD.B_eq]
        exact inf_le_left.trans hD.isMax.1
      · exact Subgroup.zpowers_le.mpr htgm
    exact hD.unique _ (sec4_isMaxElemAbelianIn_conjugate hD.isMax g hle)

private theorem exists_conj_le_sylow_of_isPGroup [Finite G] {H : Subgroup G} (P : Sylow 2 ↥H)
    {V : Subgroup G} (hVH : V ≤ H) (hVp : IsPGroup 2 V) :
    ∃ c ∈ H, ∀ x ∈ V, c⁻¹ * x * c ∈ (P : Subgroup ↥H).map H.subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp' : IsPGroup 2 (V.subgroupOf H) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  obtain ⟨Q, hQ⟩ := hVp'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H P Q
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hVH hx⟩ : H) ∈ (Q : Subgroup H) :=
    hQ (show (⟨x, hVH hx⟩ : H) ∈ V.subgroupOf H from hx)
  rw [← hc, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have hxP : (⟨(c : G)⁻¹ * x * (c : G),
      H.mul_mem (H.mul_mem (H.inv_mem c.2) (hVH hx)) c.2⟩ : H) ∈ (P : Subgroup ↥H) := by
    have h1 : c⁻¹ * (⟨x, hVH hx⟩ : H) * c ∈ (P : Subgroup ↥H) := by
      simpa [MulAut.conj_inv_apply] using hxQ
    exact h1
  exact Subgroup.mem_map_of_mem H.subtype hxP

theorem sec4_fusion_of_weakly_closed [Finite G] {t : G} {S A : Subgroup G}
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (hA : CFSG.Open.IsElemAbelian 2 A)
    (htA : t ∈ A) (hwc : ∀ g : G, CFSG.conjugate A g ≤ S → CFSG.conjugate A g = A) :
    conjClassIn ⊤ t ∩ (A : Set G) = conjClassIn (normalizer (A : Set G)) t := by
  let H : Subgroup G := centralizer ({t} : Set G)
  have hS' : IsSylow2Of S H := hS
  ext a
  constructor
  · rintro ⟨⟨h, -, rfl⟩, haA⟩
    have hAh_le : CFSG.conjugate A h ≤ H := by
      intro x hx
      rw [mem_conjugate_iff] at hx
      change x ∈ centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      haveI : IsMulCommutative ↥A := hA.1
      have hcomm : (h * x * h⁻¹) * (h * t * h⁻¹) = (h * t * h⁻¹) * (h * x * h⁻¹) :=
        congrArg Subtype.val (mul_comm' (⟨h * x * h⁻¹, hx⟩ : ↥A) ⟨h * t * h⁻¹, haA⟩)
      have h' := congrArg (fun z => h⁻¹ * z * h) hcomm
      have : x * t = t * x := by simpa [mul_assoc] using h'
      exact this.symm
    have hAhp : IsPGroup 2 (CFSG.conjugate A h) := by
      intro x
      refine ⟨1, Subtype.ext ?_⟩
      simpa using (sec4_isElemAbelian_conjugate hA h).2 (x : G) x.2
    obtain ⟨P, hP⟩ := hS'.exists_sylow
    obtain ⟨c, hcH, hcc⟩ := exists_conj_le_sylow_of_isPGroup P hAh_le hAhp
    have hfun : (MulAut.conj (h * c)⁻¹).toMonoidHom =
        (((MulAut.conj (c : G))⁻¹).toMonoidHom).comp ((MulAut.conj h⁻¹).toMonoidHom) := by
      ext x
      simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply,
        MulAut.conj_inv_apply]
      rw [mul_inv_rev]
      group
    have heq : CFSG.conjugate A (h * c) =
        (CFSG.conjugate A h).map ((MulAut.conj (c : G))⁻¹).toMonoidHom := by
      rw [CFSG.conjugate, CFSG.conjugate, Subgroup.map_map, hfun]
    have hcle : (CFSG.conjugate A h).map ((MulAut.conj (c : G))⁻¹).toMonoidHom ≤ S := by
      rw [← hP]
      intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa [MulAut.conj_inv_apply] using hcc y hy
    have hgc : CFSG.conjugate A (h * c) ≤ S := by rwa [heq]
    have hAm : CFSG.conjugate A (h * c) = A := hwc (h * c) hgc
    refine ⟨h * c, mem_normalizer_of_conjugate_eq hAm, ?_⟩
    have hct : (c : G) * t = t * c :=
      (Subgroup.mem_centralizer_iff.mp hcH t (Set.mem_singleton t)).symm
    have hctc : (c : G) * t * (c : G)⁻¹ = t := by rw [hct]; group
    rw [show (h * c) * t * (h * c)⁻¹ = h * ((c : G) * t * (c : G)⁻¹) * h⁻¹ by group, hctc]
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, trivial, rfl⟩, (Subgroup.mem_normalizer_iff.mp hm t).mp htA⟩

theorem asc82Lemma46a_of (h43 : Asc82Lemma43) (h44d : Asc82Lemma44d) (h44e : Asc82Lemma44e) :
    Asc82Lemma46a := by
  intro G _ _ t L S z hctx A hA
  have hS : S ≤ centralizer ({t} : Set G) := hctx.sylow.1
  have hAS : A ≤ S := hA.1.trans inf_le_left
  have hzL : z ∈ L := hctx.pocket.mem
  obtain ⟨htA, hzA, hAeq, -⟩ := h44e G t L S z hctx A hA
  have hALeq := h44d G t L S z hctx A hA
  have hsub : A ⊓ L ≤ Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G)) := by
    rw [hALeq]
    refine Subgroup.closure_mono ?_
    rintro w ⟨n, hn, rfl⟩
    rw [Subgroup.mem_inf] at hn
    exact ⟨⟨n, trivial, rfl⟩, (Subgroup.mem_normalizer_iff.mp hn.2 z).mp hzA⟩
  by_cases htz : ∃ g : G, g⁻¹ * z * g = t * z
  · refine Or.inl ⟨htz, le_antisymm ?_ ((Subgroup.closure_le _).mpr Set.inter_subset_right)⟩
    conv_lhs => rw [hAeq]
    refine sup_le hsub (Subgroup.zpowers_le.mpr ?_)
    have htz_mem : t * z ∈ conjClassIn ⊤ z ∩ (A : Set G) := by
      refine ⟨?_, A.mul_mem htA hzA⟩
      obtain ⟨g, hg⟩ := htz
      exact ⟨g⁻¹, trivial, by rw [inv_inv, hg]⟩
    have hz_mem : z ∈ conjClassIn ⊤ z ∩ (A : Set G) :=
      ⟨⟨1, trivial, by group⟩, hzA⟩
    rw [show t = (t * z) * z⁻¹ by group]
    exact (Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G))).mul_mem
      (Subgroup.subset_closure htz_mem)
      ((Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G))).inv_mem
        (Subgroup.subset_closure hz_mem))
  · have hCeq : conjClassIn ⊤ z ∩ (centralizer ({t} : Set G) : Set G) = conjClassIn L z := by
      refine le_antisymm ?_ ?_
      · rintro w ⟨⟨h, -, rfl⟩, hwt⟩
        have hg : (h⁻¹)⁻¹ * z * h⁻¹ = h * z * h⁻¹ := by rw [inv_inv]
        have hcase := h43 G t L S z hctx h⁻¹ (by rw [hg]; exact hwt)
        rw [hg] at hcase
        rcases hcase with hwz | hwtz
        · exact hwz
        · exfalso
          obtain ⟨l, hl, hlw⟩ := hwtz
          refine htz ⟨(l⁻¹ * h)⁻¹, ?_⟩
          rw [inv_inv]
          calc l⁻¹ * h * z * (l⁻¹ * h)⁻¹ = l⁻¹ * (h * z * h⁻¹) * l := by group
            _ = l⁻¹ * (l * (t * z) * l⁻¹) * l := by rw [hlw]
            _ = t * z := by group
      · rintro w ⟨l, hl, rfl⟩
        exact ⟨⟨l, trivial, rfl⟩,
          hctx.component.le (L.mul_mem (L.mul_mem hl hzL) (L.inv_mem hl))⟩
    refine Or.inr ⟨hCeq, le_antisymm hsub ?_⟩
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨hwz, hwA⟩
    have hwt : w ∈ centralizer ({t} : Set G) := hS (hAS hwA)
    have hmem : w ∈ conjClassIn ⊤ z ∩ (centralizer ({t} : Set G) : Set G) := ⟨hwz, hwt⟩
    rw [hCeq] at hmem
    obtain ⟨l, hl, rfl⟩ := hmem
    exact ⟨hwA, L.mul_mem (L.mul_mem hl hzL) (L.inv_mem hl)⟩

theorem asc82Lemma46b_of (h43 : Asc82Lemma43) (h46a : Asc82Lemma46a)
    (hAD : Asc82ADataExists) : Asc82Lemma46b := by
  intro G _ _ t L S z hctx A hA
  obtain ⟨A₀, B, φ, hD⟩ := hAD G t L S z hctx
  rw [hD.unique A hA]
  have htA : t ∈ A₀ := by
    rw [hD.A_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  refine ⟨fun g hg => sec4_weakly_closed h43 h46a hctx hD hg, ?_⟩
  refine sec4_fusion_of_weakly_closed hctx.sylow hD.isMax.2.1 htA ?_
  intro g hg
  exact sec4_weakly_closed h43 h46a hctx hD hg

end CFSG.OddStandard.SmallF3.Omega
