module

public import CFSG.LieType.SeitzGeneration.SpHyperCenters
public import CFSG.LieType.SeitzGeneration.HyperAveraging
public import CFSG.LieType.SeitzGeneration.HyperLeaf
public import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.RankThree.PartOne.CTP.SeitzToral

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartOne.CTP
  CFSG.Assembly.LowTwoRank CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {r : ℕ} {K : Type} [Field K]

theorem exists_stable_compl [Finite K] {A : Subgroup (StatedSp r K)} (hA : (Nat.card A : K) ≠ 0)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hW : ∀ x ∈ A, ∀ w ∈ W, spEnd x w ∈ W) :
    ∃ W' : Submodule K (Fin r ⊕ Fin r → K), IsCompl W W' ∧
      ∀ x ∈ A, ∀ w ∈ W', spEnd x w ∈ W' := by
  have : NeZero (Nat.card A : K) := ⟨hA⟩
  let ρ : Representation K A (Fin r ⊕ Fin r → K) :=
    { toFun := fun h => spEnd h.1
      map_one' := spEnd_one
      map_mul' := fun a b => spEnd_mul a.1 b.1 }
  let σ : Subrepresentation ρ := ⟨W, fun g v hv => hW g g.2 v hv⟩
  obtain ⟨σ', hσ'⟩ := exists_isCompl σ
  refine ⟨σ'.toSubmodule, ⟨?_, ?_⟩, fun x hx w hw => σ'.apply_mem_toSubmodule ⟨x, hx⟩ hw⟩
  · rw [disjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hσ'.1)
    exact this
  · rw [codisjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hσ'.2)
    exact this

theorem exists_lift_elemAbelian {G Q : Type*} [Group G] [Group Q] [Finite G] {p : ℕ}
    [Fact p.Prime] (π : G →* Q) (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker)
    {E : Subgroup Q} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1) :
    ∃ A : Subgroup G, A.map π = E ∧ Disjoint A π.ker ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      (∀ a ∈ A, a ^ p = 1) ∧ Nat.card A = Nat.card E := by
  classical
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨E', hE'map, hE'dis⟩ :=
    CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker π hπ hker E hEp
  have hE'mem : ∀ x ∈ E', π x ∈ E := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' :=
      E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha)) (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have := hcomm _ (hE'mem a ha) _ (hE'mem b hb)
      rw [this]
      group
    have := Subgroup.disjoint_def.mp hE'dis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hexp _ (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  let fπ : E' →* E := (π.comp E'.subtype).codRestrict E (fun x => hE'mem x.1 x.2)
  have hfπsurj : Function.Surjective fπ := by
    intro e
    have : (e : Q) ∈ E'.map π := hE'map ▸ e.2
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hfπinj : Function.Injective fπ := by
    intro x y hxy
    have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
    have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x.1⁻¹ * y.1 = 1 :=
      Subgroup.disjoint_def.mp hE'dis (E'.mul_mem (E'.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  exact ⟨E', hE'map, hE'dis, hE'comm, hE'exp,
    Nat.card_congr (Equiv.ofBijective fπ ⟨hfπinj, hfπsurj⟩)⟩

theorem relIndex_map_lift {G Q : Type*} [Group G] [Group Q] {π : G →* Q} {A : Subgroup G}
    {E : Subgroup Q} {p : ℕ} (hAE : A.map π = E) (hdis : Disjoint A π.ker)
    {F' : Subgroup A} (hF' : F'.index = p) :
    (F'.map (π.comp A.subtype)).relIndex E = p := by
  have hinj : Function.Injective (π.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h
    exact Subtype.ext (Subgroup.disjoint_def.mp hdis hx (by simpa using h))
  have hrange : (π.comp A.subtype).range = E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hAE]
  have h := Subgroup.relIndex_map_map_of_injective (f := π.comp A.subtype) F' ⊤ hinj
  rw [← MonoidHom.range_eq_map, hrange, Subgroup.relIndex_top_right] at h
  rw [h, hF']

theorem hyperGen_top_of_isotropic [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) (hr : 1 ≤ r) {E : Subgroup (StatedProj (StatedSp r K))}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0)
    (hstab : ∀ g : StatedSp r K, proj r K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) :
    HyperGen p (⊤ : Subgroup (StatedProj (StatedSp r K))) E := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hproj := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
    (r := r) (K := K)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hker : ¬ p ∣ Nat.card (proj r K).ker := fun hd =>
    hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (coprime_card_ker_proj hr hp hp2) hd (dvd_refl p))
  obtain ⟨A, hAE, hAdis, hAcomm, hAexp, hAcard⟩ :=
    exists_lift_elemAbelian (proj r K) hproj hker hcomm hE.2
  have hAcardp : Nat.card A = p ^ 3 := hAcard.trans hcard
  let ρ : A →* Module.End K (Fin r ⊕ Fin r → K) :=
    { toFun := fun a => spEnd a.1
      map_one' := spEnd_one
      map_mul' := fun a b => spEnd_mul a.1 b.1 }
  have hAc : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hAcomm a a.2 b b.2)
  have hAp : ∀ a : A, a ^ p = 1 := fun a => Subtype.ext (hAexp a a.2)
  have hAmem : ∀ a : A, proj r K a.1 ∈ E := fun a => by
    rw [← hAE]; exact Subgroup.mem_map_of_mem _ a.2
  have hAstab : ∀ a : A, ∀ w ∈ W, ρ a w ∈ W := fun a w hw => hstab a.1 (hAmem a) w hw
  obtain ⟨F', hF'idx, hW1⟩ : ∃ F' : Subgroup A, F'.index = p ∧ hyperFixed ρ F' ⊓ W ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hmem := mem_iSup_hyperFixed_top hpK hAc hAp ρ W hAstab (k := 3) (by norm_num) hAcardp hm
    have hbot : (⨆ (F' : Subgroup A) (_ : F'.index = p), hyperFixed ρ F' ⊓ W) = ⊥ :=
      iSup_eq_bot.2 fun F' => iSup_eq_bot.2 fun hF' => hcon F' hF'
    rw [hbot] at hmem
    exact hm0 (by simpa using hmem)
  set W₁ : Submodule K (Fin r ⊕ Fin r → K) := hyperFixed ρ F' ⊓ W with hW₁
  have hW₁mem : ∀ v, v ∈ W₁ ↔ (∀ f ∈ F', ρ f v = v) ∧ v ∈ W := fun v => by
    rw [hW₁, Submodule.mem_inf, mem_hyperFixed]
  have hW₁iso : ∀ x ∈ W₁, ∀ y ∈ W₁, spForm r K x y = 0 := fun x hx y hy =>
    hW x ((hW₁mem x).1 hx).2 y ((hW₁mem y).1 hy).2
  have hW₁stab : ∀ a : A, ∀ v ∈ W₁, ρ a v ∈ W₁ := by
    intro a v hv
    rw [hW₁mem] at hv ⊢
    refine ⟨fun f hf => ?_, hAstab a v hv.2⟩
    exact mem_hyperFixed.1 (apply_mem_hyperFixed hAc a (mem_hyperFixed.2 hv.1)) f hf
  have hW₁stab' : ∀ x ∈ A, ∀ w ∈ W₁, spEnd x w ∈ W₁ := fun x hx w hw => hW₁stab ⟨x, hx⟩ w hw
  have hP₁stab : ∀ x ∈ A, ∀ v ∈ spPerp W₁, spEnd x v ∈ spPerp W₁ := by
    intro x hx v hv
    exact spEnd_mem_spPerp (fun w hw => hW₁stab' x⁻¹ (A.inv_mem hx) w hw) hv
  have hAcardK : (Nat.card A : K) ≠ 0 := by
    rw [hAcardp]; push_cast; exact pow_ne_zero 3 hpK
  obtain ⟨C₀, hcompl, hC₀stab⟩ := exists_stable_compl hAcardK hP₁stab
  have hC₀fix : ∀ f ∈ F', ∀ c ∈ C₀, spEnd f.1 c = c := by
    intro f hf c hc
    have hd : spEnd f.1 c - c ∈ C₀ := C₀.sub_mem (hC₀stab f.1 f.2 c hc) hc
    have hdp : spEnd f.1 c - c ∈ spPerp W₁ := by
      intro w hw
      have hwf : spEnd f.1 w = w := ((hW₁mem w).1 hw).1 f hf
      rw [map_sub]
      have : spForm r K w (spEnd f.1 c) = spForm r K w c := by
        calc spForm r K w (spEnd f.1 c) = spForm r K (spEnd f.1 w) (spEnd f.1 c) := by rw [hwf]
          _ = spForm r K w c := spEnd_isometry f.1 w c
      rw [this, sub_self]
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hcompl.disjoint _ hdp hd)
  set Kset : Subgroup (StatedProj (StatedSp r K)) := Subgroup.closure
    {k : StatedProj (StatedSp r K) | k ∈ (⊤ : Subgroup _) ∧
      ∃ F₀ : Subgroup (StatedProj (StatedSp r K)), F₀ ≤ E ∧ F₀.relIndex E = p ∧
        ∀ f ∈ F₀, f * k = k * f} with hKset
  set H : Subgroup (StatedSp r K) := Kset.comap (proj r K) with hH
  have hF₀E : F'.map ((proj r K).comp A.subtype) ≤ E := by
    rintro _ ⟨f, -, rfl⟩
    exact hAmem f
  have hF₀rel := relIndex_map_lift hAE hAdis hF'idx
  have hCc : ∀ c ∈ C₀, TransCenter H c := by
    intro c hc t
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F'.map ((proj r K).comp A.subtype),
      hF₀E, hF₀rel, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    show proj r K f.1 * proj r K (spTransvection c t) =
      proj r K (spTransvection c t) * proj r K f.1
    rw [← map_mul, ← map_mul, (commute_spTransvection (hC₀fix f hf c hc) t).symm]
  have hQH : spRad W₁ hW₁iso ≤ H := by
    set Qbar : Subgroup (StatedProj (StatedSp r K)) := (spRad W₁ hW₁iso).map (proj r K)
      with hQbar
    have : Finite (StatedProj (StatedSp r K)) := Finite.of_surjective (proj r K) hproj
    have hEel : CFSG.IsElementaryAbelian p E :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE
    have hnt : Nontrivial E :=
      Finite.one_lt_card_iff_nontrivial.mp (by
        rw [hcard]; exact Nat.one_lt_pow (by norm_num) hp.one_lt)
    have hAV : E ≤ Subgroup.normalizer (Qbar : Set (StatedProj (StatedSp r K))) := by
      have hnorm : ∀ e ∈ E, ∀ v ∈ Qbar, e * v * e⁻¹ ∈ Qbar := by
        intro e he v hv
        rw [← hAE] at he
        obtain ⟨a, ha, rfl⟩ := he
        obtain ⟨q, hq, rfl⟩ := hv
        refine ⟨a * q * a⁻¹, spRad_conj_mem (fun w hw => hW₁stab' a ha w hw)
          (fun w hw => hW₁stab' a⁻¹ (A.inv_mem ha) w hw) hq, ?_⟩
        simp
      intro e he
      rw [Subgroup.mem_normalizer_iff]
      intro v
      refine ⟨fun hv => hnorm e he v hv, fun hv => ?_⟩
      have := hnorm e⁻¹ (E.inv_mem he) _ hv
      simpa [mul_assoc] using this
    have hVp : ¬ p ∣ Nat.card Qbar := fun hd =>
      not_dvd_card_spRad hp hp2 hpK (hd.trans (Subgroup.card_map_dvd _ (proj r K)))
    have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p) (A := E)
      (V := Qbar) hAV hVp
    have hle : Qbar ≤ Kset := by
      refine hgen.trans (iSup₂_le fun B hB => ?_)
      intro k hk
      rw [Subgroup.mem_inf] at hk
      refine Subgroup.subset_closure ⟨Subgroup.mem_top _, B.map E.subtype,
        Subgroup.map_subtype_le B, ?_, fun f hf => Subgroup.mem_centralizer_iff.1 hk.2 f hf⟩
      have hsub : (B.map E.subtype).subgroupOf E = B :=
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective B
      rw [Subgroup.relIndex, hsub]
      exact hB
    intro q hq
    exact hle (Subgroup.mem_map_of_mem _ hq)
  have htop : H = ⊤ := eq_top_of_spRad_of_centers hW1 hcompl hQH hCc
  intro k _
  obtain ⟨g, rfl⟩ := hproj k
  have hg : g ∈ H := htop ▸ Subgroup.mem_top g
  exact hg

end CFSG.LieType.SeitzGeneration
