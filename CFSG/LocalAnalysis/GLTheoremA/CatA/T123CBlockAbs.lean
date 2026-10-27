module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S172X
open CFSG.ComponentClassification.PerfectAutomorphisms
open scoped commutatorElement

@[expose] def Type167At (p : ℕ) (T J : Type) [Group T] [Group J] : Prop :=
  (p = 3 ∧ ∃ n : ℕ, Odd n ∧ catalogIs J (isLnA n 2) ∧
      (catalogIs T (isLnA (n + 2) 2) ∨ catalogIs T (isLnA n 8))) ∨
  (p = 3 ∧ ∃ n : ℕ, Even n ∧ catalogIs J (isOmMA n 2) ∧
      (catalogIs T (isOmPA (n + 1) 2) ∨ catalogIs T (isOmMA n 8))) ∨
  (∃ n k : ℕ, Odd n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs J (isOmPA n (2 ^ k)) ∧
      (catalogIs T (isOmMA (n + 1) (2 ^ k)) ∨ catalogIs T (isOmPA n (2 ^ (p * k))) ∨
        (p = 5 ∧ n = 3 ∧ k = 2 ∧ catalogIs T (isLnA 6 4))))

@[expose] def InnerBlockAt (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ (A : Subgroup T) (a : T), IsElemAbelian p A → Nat.card A = p ^ 2 → a ∈ A → a ≠ 1 →
    ¬ Group.IsSolvable ↥(Subgroup.centralizer (A : Set T)) →
    ∃ a' ∈ A, a' ∉ Subgroup.zpowers a ∧ ∃ P M : Subgroup T,
      IsComponentOf P (Subgroup.centralizer (A : Set T)) ∧
      IsComponentOf M (Subgroup.centralizer ({a'} : Set T)) ∧ P ≤ M ∧
      p ∣ Nat.card (↥P ⧸ Subgroup.center ↥P) ∧ p ∣ Nat.card (↥M ⧸ Subgroup.center ↥M) ∧
      a ∉ Subgroup.centralizer (M : Set T)

@[expose] def fixSub {T : Type*} [Group T] (α : MulAut T) : Subgroup T :=
  α.toMonoidHom.eqLocus (MonoidHom.id T)

theorem mem_fixSub {T : Type*} [Group T] {α : MulAut T} {t : T} : t ∈ fixSub α ↔ α t = t :=
  Iff.rfl

@[expose] def FieldBlockAt (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ α : MulAut T, α ^ p = 1 → (∀ t : T, MulAut.conj t ≠ α) →
    ∃ M : Subgroup T, IsComponentOf M (fixSub α) ∧ p ∣ Nat.card (↥M ⧸ Subgroup.center ↥M) ∧
      (∀ P : Subgroup T, P ≤ fixSub α → ⁅P, P⁆ = P → P ≤ M) ∧
      ∀ β : MulAut T, (∀ m ∈ M, β m = m) → β ∈ Subgroup.zpowers α

section Central

variable {G H : Type} [Group G] [Group H]

theorem card_center_quot_map (f : G →* H) (hf : ∀ g : G, f g = 1 → g ∈ Subgroup.center G)
    {K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    Nat.card (↥(K.map f) ⧸ Subgroup.center ↥(K.map f)) =
      Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  have hperf : Group.IsPerfect ↥K := ⟨I142N.commutator_top_of_comm_self_eq hK⟩
  have hker : (f.subgroupMap K).ker ≤ Subgroup.center ↥K := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have h1 : f k = 1 := congrArg Subtype.val hk
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hf k h1) l)
  obtain ⟨e⟩ := Y10F.quotEquiv_of_perfect_central (f.subgroupMap K) (f.subgroupMap_surjective K)
    hperf hker
  exact (Nat.card_congr e.toEquiv).symm

theorem exists_component_lift_of_commutator_le (f : G →* H)
    (hf : ∀ g : G, f g = 1 → g ∈ Subgroup.center G) {Y : Subgroup G} {C Q : Subgroup H}
    (hYC : Y.map f ≤ C) (hn : ((Y.map f).subgroupOf C).Normal) (hc : ⁅C, C⁆ ≤ Y.map f)
    (hQ : IsComponentOf Q C) : ∃ Q' : Subgroup G, IsComponentOf Q' Y ∧ Q'.map f = Q :=
  I142N.exists_component_lift f hf ((isComponentOf_iff_of_commutator_le hYC hn hc).2 hQ)

end Central

section Omega

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem glaPComponent_map_subtype {p : ℕ} (hp : p.Prime) {S : Subgroup Ω} {Y Q : Subgroup ↥S}
    (hQ : IsComponentOf Q Y) (hdvd : p ∣ Nat.card (↥Q ⧸ Subgroup.center ↥Q)) :
    GLAPComponent p (Y.map S.subtype) (Q.map S.subtype) := by
  have hQ' := (Y10F.isComponentOf_map_iff S.subtype_injective).2 hQ
  refine S12.glaPComponent_of_quasisimple' hp hQ'.2.1 hQ'.2.2 ?_
  have hk : ∀ g : ↥S, S.subtype g = 1 → g ∈ Subgroup.center ↥S := fun g hg => by
    have h1 : g = 1 := Subtype.ext hg
    rw [h1]
    exact Subgroup.one_mem _
  rw [card_center_quot_map S.subtype hk (I142N.comm_self_eq_of_commutator_top hQ.2.2.1)]
  exact hdvd

theorem mem_centralizer_of_centMod_quasisimple {p : ℕ} (hp : p.Prime) {M : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple ↥M) (hpM : p ∣ Nat.card ↥M) {x : Ω} (hc : CentMod p M x) :
    x ∈ Subgroup.centralizer (M : Set Ω) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥M := ⟨hq.1⟩
  have hcore : GLAPPrimeCore p ↥M ≤ Subgroup.center ↥M := by
    refine le_center_of_normal_of_isQuasisimple hq (GLAPPrimeCore.normal p _) fun htop => ?_
    have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥M)) := CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpM
  let α : MulAut ↥M := M.normalizerMonoidHom ⟨x, hc.1⟩
  have hα : ∀ m : ↥M, (α m : Ω) = x * m * x⁻¹ := fun m => rfl
  have hdisp : ∀ m : ↥M, m⁻¹ * α m ∈ Subgroup.center ↥M := by
    intro m
    have h1 : ⁅(m : Ω)⁻¹, x⁆ ∈ GLAPPrimeCoreOf p M :=
      hc.2 (Subgroup.commutator_mem_commutator (M.inv_mem m.2) (Subgroup.mem_zpowers x))
    change ⁅(m : Ω)⁻¹, x⁆ ∈ (GLAPPrimeCore p ↥M).map M.subtype at h1
    obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.1 h1
    have he : m⁻¹ * α m = o := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hα]
      have hoe' : (o : Ω) = ⁅(m : Ω)⁻¹, x⁆ := hoe
      rw [hoe', commutatorElement_def, inv_inv]
      group
    rw [he]
    exact hcore ho
  have hid := hom_eq_id_of_central_displacement α.toMonoidHom hdisp
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have h2 : (α ⟨m, hm⟩ : Ω) = m :=
    congrArg (fun f : ↥M →* ↥M => ((f ⟨m, hm⟩ : ↥M) : Ω)) hid
  rw [hα] at h2
  calc m * x = x * m * x⁻¹ * x := by rw [h2]
    _ = x * m := by group

theorem cs_zpowers (g : Ω) : cs (Subgroup.zpowers g) = cx g := by
  rw [Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_closure {g}

end Omega

section Fix

variable {G : Type} [Group G]

theorem map_fixSub_le (φ : MulAut G) :
    (fixSub φ).map (QuotientGroup.mk' (Subgroup.center G)) ≤ fixSub (centerQuotientHom G φ) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_fixSub]
  show onCenterQuotient φ (QuotientGroup.mk' _ s) = _
  rw [onCenterQuotient_apply_mk, mem_fixSub.1 hs]

theorem commutator_mem_fixSub {φ : MulAut G} {s c : G}
    (hs : QuotientGroup.mk' (Subgroup.center G) s ∈ fixSub (centerQuotientHom G φ))
    (hc : QuotientGroup.mk' (Subgroup.center G) c ∈ fixSub (centerQuotientHom G φ)) :
    ⁅s, c⁆ ∈ fixSub φ := by
  have key : ∀ u : G, QuotientGroup.mk' (Subgroup.center G) u ∈ fixSub (centerQuotientHom G φ) →
      ∃ z ∈ Subgroup.center G, φ u = z * u := by
    intro u hu
    have h1 : QuotientGroup.mk' (Subgroup.center G) (φ u) =
        QuotientGroup.mk' (Subgroup.center G) u := by
      rw [← onCenterQuotient_apply_mk]
      exact hu
    have h2 : (φ u)⁻¹ * u ∈ Subgroup.center G := QuotientGroup.eq.1 h1
    have h3 : u * (φ u)⁻¹ ∈ Subgroup.center G := by
      have hc := Subgroup.mem_center_iff.1 h2 u
      have e : u * (φ u)⁻¹ = (φ u)⁻¹ * u := by
        calc u * (φ u)⁻¹ = u * ((φ u)⁻¹ * u) * u⁻¹ := by group
          _ = (φ u)⁻¹ * u * u * u⁻¹ := by rw [hc]
          _ = (φ u)⁻¹ * u := by group
      rw [e]
      exact h2
    refine ⟨(u * (φ u)⁻¹)⁻¹, Subgroup.inv_mem _ h3, by group⟩
  obtain ⟨z, hz, hzs⟩ := key s hs
  obtain ⟨z', hz', hzc⟩ := key c hc
  rw [mem_fixSub, map_commutatorElement, hzs, hzc, I142N.comm_central_mul_left hz,
    I142N.comm_central_mul_right hz']

theorem map_fixSub_normal (φ : MulAut G) :
    (((fixSub φ).map (QuotientGroup.mk' (Subgroup.center G))).subgroupOf
      (fixSub (centerQuotientHom G φ))).Normal := by
  refine ⟨fun y hy g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hy ⊢
  obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.1 hy
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) (g : G ⧸ Subgroup.center G)
  have hca : ⁅a, c⁆ ∈ fixSub φ := by
    refine commutator_mem_fixSub (by rw [ha]; exact g.2) ?_
    exact map_fixSub_le φ (Subgroup.mem_map_of_mem _ hc)
  refine Subgroup.mem_map.2 ⟨a * c * a⁻¹, ?_, ?_⟩
  · have e : a * c * a⁻¹ = ⁅a, c⁆ * c := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hca hc
  · rw [map_mul, map_mul, map_inv, ha, hcy]
    rfl

theorem commutator_fixSub_le (φ : MulAut G) :
    ⁅fixSub (centerQuotientHom G φ), fixSub (centerQuotientHom G φ)⁆ ≤
      (fixSub φ).map (QuotientGroup.mk' (Subgroup.center G)) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) g
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) h
  rw [← map_commutatorElement]
  exact Subgroup.mem_map_of_mem _ (commutator_mem_fixSub hg hh)

end Fix

section Blocks

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem fixSub_normalizerMonoidHom {S : Subgroup Ω} (g : ↥(Subgroup.normalizer (S : Set Ω))) :
    fixSub (S.normalizerMonoidHom g) = (S ⊓ cx (g : Ω)).subgroupOf S := by
  ext s
  rw [mem_fixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  have hcoe : ((S.normalizerMonoidHom g s : ↥S) : Ω) = g * s * (g : Ω)⁻¹ := rfl
  constructor
  · intro h
    have h1 : (g : Ω) * s * (g : Ω)⁻¹ = s := by rw [← hcoe, h]
    refine ⟨s.2, ?_⟩
    calc (s : Ω) * g = (g : Ω) * s * (g : Ω)⁻¹ * g := by rw [h1]
      _ = g * s := by group
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [hcoe, ← h]
    group

theorem centerQuotientHom_normalizerMonoidHom_mem {S : Subgroup Ω} (s : ↥S) :
    centerQuotientHom ↥S (S.normalizerMonoidHom ⟨s, Subgroup.le_normalizer s.2⟩) =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥S) s) := by
  ext t
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥S) t
  show onCenterQuotient _ (QuotientGroup.mk' _ u) = _
  rw [onCenterQuotient_apply_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem blockFact_inner {p : ℕ} (hp : p.Prime) {S D : Subgroup Ω} {x : Ω} (hSn : S.Normal)
    (hinn : InnerBlockAt p (↥S ⧸ Subgroup.center ↥S))
    (hDin : ∀ d ∈ D, d ∈ S ⊔ Subgroup.centralizer (S : Set Ω))
    (hDS : ∀ d ∈ D, d ∈ Subgroup.centralizer (S : Set Ω) → d = 1)
    (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) (hxD : x ∈ D) (hx1 : x ≠ 1)
    (hlay : GLAPLayer p (S ⊓ cs D) ≠ ⊥) :
    ∃ x' ∈ D, x' ∉ Subgroup.zpowers x ∧ ∃ P M : Subgroup Ω,
      GLAPComponent p (S ⊓ cs D) P ∧ GLAPComponent p (S ⊓ cx x') M ∧ P ≤ M ∧
        ¬ CentMod p M x := by
  obtain ⟨Mo⟩ := S172Model.nonempty_of_mem_sup (B := D) hSn hDin
    (MulEquiv.refl (↥S ⧸ Subgroup.center ↥S))
  have hπk : ∀ s : ↥S, Mo.π s = 1 → s ∈ Subgroup.center ↥S := fun s hs =>
    Mo.π_eq_one_mem_center hs
  have hβinj : Function.Injective Mo.β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    exact Subtype.ext (hDS d d.2 ((Mo.β_eq_one_iff d).1 hd))
  set A := Mo.img D with hAdef
  have hArange : A = Mo.β.range := by
    rw [hAdef, S172Model.img, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  have hmemA : ∀ g, g ∈ A ↔ ∃ d : ↥D, Mo.β d = g := fun g => by
    rw [hArange]
    exact MonoidHom.mem_range
  have hAe : IsElemAbelian p A := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨d₁, hd₁⟩ := (hmemA _).1 a.2
      obtain ⟨d₂, hd₂⟩ := (hmemA _).1 b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hd₁, ← hd₂, ← map_mul, ← map_mul]
      congr 1
      exact hD.1.is_comm.comm d₁ d₂
    · obtain ⟨d, rfl⟩ := (hmemA _).1 ha
      rw [← map_pow]
      have h1 : d ^ p = 1 := Subtype.ext (hD.2 d d.2)
      rw [h1, map_one]
  have hAc : Nat.card A = p ^ 2 := by
    rw [hArange, ← hDc]
    exact (Nat.card_congr (MonoidHom.ofInjective hβinj).toEquiv).symm
  set a := Mo.β ⟨x, hxD⟩ with hadef
  have haA : a ∈ A := (hmemA a).2 ⟨⟨x, hxD⟩, rfl⟩
  have ha1 : a ≠ 1 := by
    intro h
    apply hx1
    have h1 : (⟨x, hxD⟩ : ↥D) = 1 := hβinj (by rw [← hadef, h, map_one])
    exact congrArg Subtype.val h1
  have hns : ¬ Group.IsSolvable ↥(Subgroup.centralizer (A : Set (↥S ⧸ Subgroup.center ↥S))) := by
    intro hsol
    exact hlay (Mo.glaPLayer_eq_bot_of_csImg_le hp (Mo.csImg_le_centralizer_img D) le_rfl)
  obtain ⟨a', ha'A, ha'x, Ph, Mh, hPh, hMh, hPM, hPd, hMd, haM⟩ :=
    hinn A a hAe hAc haA ha1 hns
  obtain ⟨b', -, hb'⟩ := Mo.mem_img.1 ha'A
  set x' : Ω := (b' : Ω) with hx'def
  have hx'D : x' ∈ D := b'.2
  have hb'eq : (⟨x', hx'D⟩ : ↥D) = b' := rfl
  have hx'x : x' ∉ Subgroup.zpowers x := by
    intro h
    apply ha'x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← hb', hadef, ← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk)
  obtain ⟨P', hP', hP'm⟩ := exists_component_lift_of_commutator_le Mo.π hπk
    (Mo.csImg_le_centralizer_img D) (Mo.csImg_normal le_rfl)
    (Mo.commutator_centralizer_img_le le_rfl) hPh
  have hP'p : ⁅P', P'⁆ = P' := I142N.comm_self_eq_of_commutator_top hP'.2.2.1
  have hP'd : p ∣ Nat.card (↥P' ⧸ Subgroup.center ↥P') := by
    rw [← card_center_quot_map Mo.π hπk hP'p, hP'm]
    exact hPd
  have hP := glaPComponent_map_subtype hp hP' hP'd
  rw [map_csIn_subtype] at hP
  have himg : Mo.img (Subgroup.zpowers x') = Subgroup.zpowers a' := by
    rw [Mo.img_zpowers hx'D, hb'eq, hb']
  have hcent : Subgroup.centralizer ({a'} : Set (↥S ⧸ Subgroup.center ↥S)) =
      Subgroup.centralizer (Mo.img (Subgroup.zpowers x') : Set (↥S ⧸ Subgroup.center ↥S)) := by
    rw [himg, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent] at hMh
  have hx'B : Subgroup.zpowers x' ≤ D := Subgroup.zpowers_le.2 hx'D
  obtain ⟨M', hM', hM'm⟩ := exists_component_lift_of_commutator_le Mo.π hπk
    (Mo.csImg_le_centralizer_img _) (Mo.csImg_normal hx'B)
    (Mo.commutator_centralizer_img_le hx'B) hMh
  have hM'p : ⁅M', M'⁆ = M' := I142N.comm_self_eq_of_commutator_top hM'.2.2.1
  have hM'd : p ∣ Nat.card (↥M' ⧸ Subgroup.center ↥M') := by
    rw [← card_center_quot_map Mo.π hπk hM'p, hM'm]
    exact hMd
  have hM := glaPComponent_map_subtype hp hM' hM'd
  rw [map_csIn_subtype, cs_zpowers] at hM
  refine ⟨x', hx'D, hx'x, P'.map S.subtype, M'.map S.subtype, hP, hM, ?_, ?_⟩
  · refine Subgroup.map_mono (le_of_map_le_of_perfect Mo.π hπk hP'p ?_)
    rw [hP'm, hM'm]
    exact hPM
  · intro hc
    have hMq := ((Y10F.isComponentOf_map_iff S.subtype_injective).2 hM').2.2
    have hk : ∀ g : ↥S, S.subtype g = 1 → g ∈ Subgroup.center ↥S := fun g hg => by
      have h1 : g = 1 := Subtype.ext hg
      rw [h1]
      exact Subgroup.one_mem _
    have hMd' : p ∣ Nat.card (↥(M'.map S.subtype) ⧸ Subgroup.center ↥(M'.map S.subtype)) := by
      rw [card_center_quot_map S.subtype hk hM'p]
      exact hM'd
    have hxc := mem_centralizer_of_centMod_quasisimple hp hMq
      (hMd'.trans (Subgroup.card_quotient_dvd_card _)) hc
    haveI : Group.IsPerfect ↥M' := ⟨hM'.2.2.1⟩
    have h1 := (Mo.mem_centralizer_map_iff (K := M') inferInstance ⟨x, hxD⟩).1 hxc
    rw [hM'm] at h1
    exact haM h1

theorem blockFact_field {p : ℕ} (hp : p.Prime) {S D : Subgroup Ω} {x x' : Ω}
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hfld : FieldBlockAt p (↥S ⧸ Subgroup.center ↥S))
    (hDN : D ≤ Subgroup.normalizer (S : Set Ω))
    (hDS : ∀ d ∈ D, d ∈ Subgroup.centralizer (S : Set Ω) → d = 1)
    (hD : IsElemAbelian p D) (hxD : x ∈ D) (hx1 : x ≠ 1) (hx'D : x' ∈ D)
    (hx'x : x' ∉ Subgroup.zpowers x) (hx' : x' ∉ S ⊔ Subgroup.centralizer (S : Set Ω))
    (hlay : GLAPLayer p (S ⊓ cs D) ≠ ⊥) :
    ∃ P M : Subgroup Ω, GLAPComponent p (S ⊓ cs D) P ∧ GLAPComponent p (S ⊓ cx x') M ∧
      P ≤ M ∧ ¬ CentMod p M x := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥S := ⟨hSq.1⟩
  set π := QuotientGroup.mk' (Subgroup.center ↥S) with hπdef
  have hπk : ∀ s : ↥S, π s = 1 → s ∈ Subgroup.center ↥S := fun s hs =>
    (QuotientGroup.eq_one_iff s).1 hs
  set ρ := (centerQuotientHom ↥S).comp S.normalizerMonoidHom with hρdef
  set g' : ↥(Subgroup.normalizer (S : Set Ω)) := ⟨x', hDN hx'D⟩ with hg'def
  set gx : ↥(Subgroup.normalizer (S : Set Ω)) := ⟨x, hDN hxD⟩ with hgxdef
  set φ' := S.normalizerMonoidHom g' with hφ'def
  have hρ1 : ∀ g : ↥(Subgroup.normalizer (S : Set Ω)),
      ρ g = 1 ↔ (g : Ω) ∈ Subgroup.centralizer (S : Set Ω) := fun g =>
    S172A.normalizer_action_eq_one_iff g
  have hpow : ρ g' ^ p = 1 := by
    rw [← map_pow]
    have h1 : g' ^ p = 1 := Subtype.ext (by simpa using hD.2 x' hx'D)
    rw [h1, map_one]
  have hout : ∀ t : ↥S ⧸ Subgroup.center ↥S, MulAut.conj t ≠ ρ g' := by
    intro t ht
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥S) t
    set gs : ↥(Subgroup.normalizer (S : Set Ω)) := ⟨s, Subgroup.le_normalizer s.2⟩
    have hgs : ρ gs = MulAut.conj (π s) := centerQuotientHom_normalizerMonoidHom_mem s
    have h1 : ρ (gs⁻¹ * g') = 1 := by
      rw [map_mul, map_inv, hgs, ht, inv_mul_cancel]
    have h2 := (hρ1 _).1 h1
    apply hx'
    have e : x' = (s : Ω) * ((gs⁻¹ * g' : ↥(Subgroup.normalizer (S : Set Ω))) : Ω) := by
      simp [gs, g']
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left s.2) (Subgroup.mem_sup_right h2)
  obtain ⟨Mh, hMh, hMd, hperf, hstab⟩ := hfld (ρ g') hpow hout
  obtain ⟨M', hM', hM'm⟩ := exists_component_lift_of_commutator_le π hπk (map_fixSub_le φ')
    (map_fixSub_normal φ') (commutator_fixSub_le φ') hMh
  have hM'p : ⁅M', M'⁆ = M' := I142N.comm_self_eq_of_commutator_top hM'.2.2.1
  have hM'd : p ∣ Nat.card (↥M' ⧸ Subgroup.center ↥M') := by
    rw [← card_center_quot_map π hπk hM'p, hM'm]
    exact hMd
  have hM := glaPComponent_map_subtype hp hM' hM'd
  have hfix : (fixSub φ').map S.subtype = S ⊓ cx x' := by
    rw [hφ'def, fixSub_normalizerMonoidHom]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
  rw [hfix] at hM
  obtain ⟨P, hP⟩ := T123C.exists_pComponent_of_layer_ne_bot hlay
  have hPS : P ≤ S := hP.1.trans inf_le_left
  have hPx' : P ≤ S ⊓ cx x' := le_inf hPS (hP.1.trans (inf_le_right.trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hx'D))))
  set P' := P.subgroupOf S with hP'def
  have hP'map : P'.map S.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPS
  have hP'p : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator, hP'map]
    exact glaPComponent_perfect hP
  have hP'fix : P' ≤ fixSub φ' := by
    rw [hφ'def, fixSub_normalizerMonoidHom]
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact hPx' hs
  have hP'M : P'.map π ≤ Mh := by
    refine hperf _ ((Subgroup.map_mono hP'fix).trans (map_fixSub_le φ')) ?_
    rw [← Subgroup.map_commutator, hP'p]
  refine ⟨P, M'.map S.subtype, hP, hM, ?_, ?_⟩
  · rw [← hP'map]
    refine Subgroup.map_mono (le_of_map_le_of_perfect π hπk hP'p ?_)
    rw [hM'm]
    exact hP'M
  · intro hc
    have hMq := ((Y10F.isComponentOf_map_iff S.subtype_injective).2 hM').2.2
    have hk : ∀ g : ↥S, S.subtype g = 1 → g ∈ Subgroup.center ↥S := fun g hg => by
      have h1 : g = 1 := Subtype.ext hg
      rw [h1]
      exact Subgroup.one_mem _
    have hMd' : p ∣ Nat.card (↥(M'.map S.subtype) ⧸ Subgroup.center ↥(M'.map S.subtype)) := by
      rw [card_center_quot_map S.subtype hk hM'p]
      exact hM'd
    have hxc := mem_centralizer_of_centMod_quasisimple hp hMq
      (hMd'.trans (Subgroup.card_quotient_dvd_card _)) hc
    have hfixM : ∀ m ∈ Mh, ρ gx m = m := by
      intro m hm
      rw [← hM'm] at hm
      obtain ⟨m', hm', rfl⟩ := hm
      show onCenterQuotient (S.normalizerMonoidHom gx) (π m') = π m'
      rw [onCenterQuotient_apply_mk]
      congr 1
      apply Subtype.ext
      have hcomm := Subgroup.mem_centralizer_iff.1 hxc (m' : Ω) (Subgroup.mem_map_of_mem _ hm')
      show x * (m' : Ω) * x⁻¹ = m'
      rw [← hcomm]
      group
    obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.1 (hstab (ρ gx) hfixM)
    have h1 : ρ (g' ^ k * gx⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk', mul_inv_cancel]
    have h2 := (hρ1 _).1 h1
    have h3 : x' ^ k * x⁻¹ ∈ D := D.mul_mem (D.zpow_mem hx'D k) (D.inv_mem hxD)
    have h4 : x' ^ k * x⁻¹ = 1 := hDS _ h3 (by simpa [g', gx] using h2)
    have hxx' : x ∈ Subgroup.zpowers x' :=
      Subgroup.mem_zpowers_iff.2 ⟨k, (mul_inv_eq_one.1 h4)⟩
    have hx'1 : x' ≠ 1 := fun h => hx'x (h ▸ Subgroup.one_mem _)
    have hord : orderOf x' = p := orderOf_eq_prime (hD.2 x' hx'D) hx'1
    exact hx'x (S12.mem_zpowers_of_prime_order hord hxx' hx1)

end Blocks

section Reduction

variable {G : Type} [Group G]

theorem type167At_of_type167 {p : ℕ} {X J : Subgroup G} {T : Type} [Group T]
    (e : T ≃* PSimple p X) (h : Type167 p X J) : Type167At p T (PSimple p J) := by
  rcases h with ⟨rfl, n, hn, hJ, hX | hX⟩ | ⟨rfl, n, hn, hJ, hX | hX⟩ |
      ⟨n, k, hn, hk, hdvd, hJ, hX | hX | ⟨h5, hn3, hk2, hX⟩⟩
  · exact Or.inl ⟨rfl, n, hn, hJ, Or.inl ((catalogIs_congr e).2 hX)⟩
  · exact Or.inl ⟨rfl, n, hn, hJ, Or.inr ((catalogIs_congr e).2 hX)⟩
  · exact Or.inr (Or.inl ⟨rfl, n, hn, hJ, Or.inl ((catalogIs_congr e).2 hX)⟩)
  · exact Or.inr (Or.inl ⟨rfl, n, hn, hJ, Or.inr ((catalogIs_congr e).2 hX)⟩)
  · exact Or.inr (Or.inr ⟨n, k, hn, hk, hdvd, hJ, Or.inl ((catalogIs_congr e).2 hX)⟩)
  · exact Or.inr (Or.inr ⟨n, k, hn, hk, hdvd, hJ, Or.inr (Or.inl ((catalogIs_congr e).2 hX))⟩)
  · exact Or.inr (Or.inr ⟨n, k, hn, hk, hdvd, hJ,
      Or.inr (Or.inr ⟨h5, hn3, hk2, (catalogIs_congr e).2 hX⟩)⟩)

theorem exists_mem_not_mem_not_mem {D H₁ H₂ : Subgroup G} {u v : G} (hu : u ∈ D) (hu1 : u ∉ H₁)
    (hv : v ∈ D) (hv2 : v ∉ H₂) : ∃ w ∈ D, w ∉ H₁ ∧ w ∉ H₂ := by
  by_cases hu2 : u ∈ H₂
  · by_cases hv1 : v ∈ H₁
    · refine ⟨u * v, D.mul_mem hu hv, fun h => hu1 ?_, fun h => hv2 ?_⟩
      · have e : u = u * v * v⁻¹ := by group
        rw [e]
        exact H₁.mul_mem h (H₁.inv_mem hv1)
      · have e : v = u⁻¹ * (u * v) := by group
        rw [e]
        exact H₂.mul_mem (H₂.inv_mem hu2) h
    · exact ⟨v, hv, hv1, hv2⟩
  · exact ⟨u, hu, hu1, hu2⟩

end Reduction

theorem blockFact_of_models
    (hmod : ∀ (p : ℕ) (T J : Type) [Group T] [Group J] [Finite T], p.Prime → p ≠ 2 →
      Type167At p T J → InnerBlockAt p T ∧ FieldBlockAt p T) : T123C.BlockFact := by
  intro p Ω _ _ S B K₁ D₁ D x y hp hp2 hSn hSq htype hK₁ hB hBN hSC hxB hx1 hyB hBS hyc hD₁ hD₁K
    hD hxD hE3 hlay
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥S := ⟨hSq.1⟩
  have hpK₁ : p ∣ Nat.card K₁ := by
    by_contra hnd
    apply S12.glaPPrimeCore_ne_top_of_glaPComponent hK₁
    refine top_le_iff.1 (le_sSup ⟨inferInstance, ?_⟩)
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  have hpS : p ∣ Nat.card S :=
    hpK₁.trans (Subgroup.card_dvd_of_le (hK₁.1.trans inf_le_left))
  have hO : GLAPPrimeCore p ↥S ≤ Subgroup.center ↥S := by
    refine le_center_of_normal_of_isQuasisimple hSq (GLAPPrimeCore.normal p _) fun htop => ?_
    have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥S)) := CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpS
  obtain ⟨hinn, hfld⟩ := hmod p (↥S ⧸ Subgroup.center ↥S) (PSimple p K₁) hp hp2
    (type167At_of_type167 (S172A.pSimpleEquivCenterQuot p hO) htype)
  have hDB : D ≤ B := hD.1
  have hyD : y ∉ D := by
    intro hyD
    have hle : D₁ ≤ D := by
      rw [← hD₁]
      refine (Subgroup.closure_le D).2 ?_
      intro z hz
      rcases hz with rfl | hz
      · exact hxD
      · rw [Set.mem_singleton_iff.1 hz]
        exact hyD
    have h1 := hE3.2.2
    rw [sup_eq_left.2 hle, hD.2.2] at h1
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hyord : orderOf y = p := by rw [← Nat.card_zpowers]; exact hyc
  have hDS : ∀ d ∈ D, d ∈ Subgroup.centralizer (S : Set Ω) → d = 1 := by
    intro d hd hdc
    by_contra hd1
    have hdy : d ∈ Subgroup.zpowers y := by
      rw [← hBS]
      exact ⟨hDB hd, hdc⟩
    exact hyD (Subgroup.zpowers_le.2 hd (S12.mem_zpowers_of_prime_order hyord hdy hd1))
  by_cases hin : ∀ d ∈ D, d ∈ S ⊔ Subgroup.centralizer (S : Set Ω)
  · exact blockFact_inner hp hSn hinn hin hDS hD.2.1 hD.2.2 hxD hx1 hlay
  · push Not at hin
    obtain ⟨d₀, hd₀D, hd₀⟩ := hin
    obtain ⟨v, hvD, hvx⟩ : ∃ v ∈ D, v ∉ Subgroup.zpowers x := by
      by_contra hcon
      push Not at hcon
      have hle : D ≤ Subgroup.zpowers x := hcon
      have h1 := Subgroup.card_le_of_le hle
      rw [hD.2.2, Nat.card_zpowers, orderOf_eq_prime (hD.2.1.2 x hxD) hx1] at h1
      have h2 : p < p ^ 2 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
    obtain ⟨x', hx'D, hx'S, hx'x⟩ := exists_mem_not_mem_not_mem hd₀D hd₀ hvD hvx
    obtain ⟨P, M, hP, hM, hPM, hnc⟩ := blockFact_field hp hSq hfld (hDB.trans hBN) hDS hD.2.1
      hxD hx1 hx'D hx'x hx'S hlay
    exact ⟨x', hx'D, hx'x, P, M, hP, hM, hPM, hnc⟩

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
