module

public import CFSG.LocalAnalysis.OddStandard.Seitz77V1ActRadical
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionDefs
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Act

public section

namespace CFSG.OddStandard.Seitz77.V1Act

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification CFSG.PSL3Four
  CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

section Pullback

variable {G : Type*} [Group G] {A V V₁ V₂ : Subgroup G}
  (g : normalizer (A : Set G) →* Equiv.Perm (Fin 42))

theorem exists_radical_image (hR : Radicals V V₁ V₂) (hVA : V ≤ A)
    (hinj : ∀ n n' : normalizer (A : Set G), (n : G) ∈ V → (n' : G) ∈ V → g n = g n' → n = n')
    {X : Subgroup (Equiv.Perm (Fin 42))}
    (hX : X ≤ (V.subgroupOf (normalizer (A : Set G))).map g) (hXel : IsElemAbelian 2 X)
    (hX16 : Nat.card X = 16) :
    ∃ W : Subgroup G, (W = V₁ ∨ W = V₂) ∧
      (W.subgroupOf (normalizer (A : Set G))).map g = X := by
  have hVN : ∀ v ∈ V, v ∈ normalizer (A : Set G) := fun v hv => le_normalizer (hVA hv)
  let ιV : ↥V →* Equiv.Perm (Fin 42) := g.comp (Subgroup.inclusion (hVA.trans le_normalizer))
  have hιinj : Function.Injective ιV := by
    intro v v' h
    have h' := congrArg Subtype.val (hinj ⟨v, hVN v v.2⟩ ⟨v', hVN v' v'.2⟩ v.2 v'.2 h)
    exact Subtype.ext h'
  have hrange : ιV.range = (V.subgroupOf (normalizer (A : Set G))).map g := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨⟨v, hVN v v.2⟩, Subgroup.mem_subgroupOf.2 v.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, Subgroup.mem_subgroupOf.1 hn⟩, rfl⟩
  have hXr : X ≤ ιV.range := hrange ▸ hX
  let W : Subgroup G := (X.comap ιV).map V.subtype
  have hWV : W ≤ V := Subgroup.map_subtype_le _
  have hWel : IsElemAbelian 2 W :=
    L34.isElemAbelian_map _ (L34.isElemAbelian_comap hιinj hXel)
  have hWcard : Nat.card W = 16 := by
    have h1 : Nat.card W = Nat.card ↥(X.comap ιV) :=
      Subgroup.card_map_of_injective V.subtype_injective
    have h2 : Nat.card ↥((X.comap ιV).map ιV) = Nat.card ↥(X.comap ιV) :=
      Subgroup.card_map_of_injective hιinj
    rw [Subgroup.map_comap_eq_self hXr] at h2
    rw [h1, ← h2, hX16]
  refine ⟨W, hR.eq_of_card W hWV hWel hWcard, ?_⟩
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨v, hv, hvn⟩ : (n : G) ∈ W := Subgroup.mem_subgroupOf.1 hn
    have hn' : n = ⟨v, hVN v v.2⟩ := Subtype.ext hvn.symm
    rw [hn']
    exact hv
  · intro hy
    obtain ⟨v, hv⟩ := hXr hy
    refine ⟨⟨v, hVN v v.2⟩, Subgroup.mem_subgroupOf.2 ⟨v, ?_, rfl⟩, hv⟩
    show ιV v ∈ X
    rw [hv]
    exact hy

end Pullback

theorem mem_conjSub {F : Subgroup (Equiv.Perm (Fin 42))} {t y : Equiv.Perm (Fin 42)} :
    y ∈ F.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * y * t ∈ F := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem exists_radicalIdent {G : Type*} [Group G] [Finite G]
    {A V V₁ V₂ W : Subgroup G} (hA : commutator ↥A = ⊤) (hZ : Odd (Nat.card (center ↥A)))
    (e : ↥A ⧸ center ↥A ≃* ↥S) (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) (hsyl : l34SylCheck (enumBFS 42 gensS 20160).tabs = true)
    (hcheck : Certificates.Seitz77L34.l34FCentCheck (enumBFS 42 gTabs 241920).tabs = true) :
    Nonempty (RadicalIdent A W) := by
  classical
  have hVA : V ≤ A := hV.le
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoL3Four.HypII.l34AutModel hA e
  obtain ⟨g, hg⟩ : ∃ g : ↥(normalizer (A : Set G)) →* Equiv.Perm (Fin 42),
      ∀ n, g n = (ψ n : Equiv.Perm (Fin 42)) := ⟨R.subtype.comp ψ, fun n => rfl⟩
  have hgR : ∀ n, g n ∈ R := fun n => by rw [hg]; exact (ψ n).2
  have hker : ∀ n : normalizer (A : Set G), g n = 1 ↔ (n : G) ∈ centralizer (A : Set G) := by
    intro n
    rw [hg, ← hψ.eq_one_iff n]
    exact OneMemClass.coe_eq_one
  have hodd : Odd (Nat.card ↥(A ⊓ centralizer (A : Set G))) := by
    have hcard : Nat.card ↥(A ⊓ centralizer (A : Set G)) = Nat.card ↥(center ↥A) := by
      rw [← map_center_subtype_eq_inf_centralizer A]
      exact Subgroup.card_map_of_injective A.subtype_injective
    rw [hcard]
    exact hZ
  have hV1 : ∀ v ∈ V, v ∈ centralizer (A : Set G) → v = 1 := by
    intro v hv hvc
    have hdvd : orderOf v ∣ Nat.card ↥(A ⊓ centralizer (A : Set G)) :=
      Subgroup.orderOf_dvd_natCard (A ⊓ centralizer (A : Set G)) ⟨hVA hv, hvc⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hV.isPGroup ⟨v, hv⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa using hk
    · exfalso
      have h2 : 2 ∣ orderOf v := by
        rw [hk]
        exact dvd_pow_self 2 hkpos.ne'
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hdvd))
  have hWV : W ≤ V ∧ IsElemAbelian 2 W ∧ Nat.card W = 16 := hR.property hW
  have hginj : ∀ n n' : normalizer (A : Set G), (n : G) ∈ V → (n' : G) ∈ V → g n = g n' →
      n = n' := by
    intro n n' hn hn' h
    have h1 : g (n⁻¹ * n') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : (n : G)⁻¹ * n' ∈ centralizer (A : Set G) := (hker _).1 h1
    have h3 : (n : G)⁻¹ * n' ∈ V := V.mul_mem (V.inv_mem hn) hn'
    have h4 := hV1 _ h3 h2
    have : (n : G) = n' := inv_mul_eq_one.1 h4
    exact Subtype.ext this
  have hVN : IsSylowOf 2 (V.subgroupOf (normalizer (A : Set G)))
      (A.subgroupOf (normalizer (A : Set G))) := by
    refine (isSylowOf_map_subtype_iff (normalizer (A : Set G))).1 ?_
    rwa [Subgroup.map_subgroupOf_eq_of_le (hVA.trans le_normalizer),
      Subgroup.map_subgroupOf_eq_of_le le_normalizer]
  have himg := L34.isSylowOf_map hVN g
  have hAimg : (A.subgroupOf (normalizer (A : Set G))).map g = S := by
    ext s
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hg]
      exact hψ.map_mem a ha
    · intro hs
      obtain ⟨a, ha, hax⟩ := hψ.exists_eq ⟨s, S_le_R hs⟩ (Subgroup.mem_subgroupOf.2 hs)
      exact ⟨⟨a, le_normalizer ha⟩, ha, by rw [hg, hax]⟩
  rw [hAimg] at himg
  obtain ⟨P, F, hF, hPS, hcardP, hFP, hcardF, hFcomm, hFsq, hr3P⟩ :=
    l34SylCheck_spec enumerates_S hsyl
  have hPsyl : IsSylowOf 2 P S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine isSylowOf_iff.2 ⟨hPS, IsPGroup.of_card (n := 6) (by rw [hcardP]; norm_num), ?_⟩
    have h1 := Subgroup.relIndex_mul_card (H := P) (K := S)
    rw [inf_eq_left.2 hPS, hcardP, card_S] at h1
    have : P.relIndex S = 315 := by omega
    rw [this]
    norm_num
  obtain ⟨s, hsS, hs⟩ := hPsyl.exists_mem_conj himg
  obtain ⟨hFcent, hr3F⟩ := l34FCentCheck_spec hF enumerates_R hcheck
  have hr3r3 : r₃ * r₃ = 1 := Equiv.ext g6Fun_g6Fun
  have hr3i : r₃⁻¹ = r₃ := inv_eq_of_mul_eq_one_right hr3r3
  have hFel : IsElemAbelian 2 F :=
    L34.isElemAbelian_of_forall hFcomm fun x hx => by simpa [sq] using hFsq x hx
  have hX₁ : F.map (MulAut.conj s).toMonoidHom ≤ (V.subgroupOf (normalizer (A : Set G))).map g := by
    intro y hy
    exact (hs y).2 (hFP (mem_conjSub.1 hy))
  have hX₂ : F.map (MulAut.conj (s * r₃)).toMonoidHom ≤
      (V.subgroupOf (normalizer (A : Set G))).map g := by
    intro y hy
    refine (hs y).2 ?_
    have h1 := hr3P _ (hFP (mem_conjSub.1 hy))
    have e : r₃ * ((s * r₃)⁻¹ * y * (s * r₃)) * r₃⁻¹ = s⁻¹ * y * s := by group
    rwa [e] at h1
  have hel : ∀ t : Equiv.Perm (Fin 42), IsElemAbelian 2 (F.map (MulAut.conj t).toMonoidHom) :=
    fun t => L34.isElemAbelian_map _ hFel
  have hcard : ∀ t : Equiv.Perm (Fin 42), Nat.card ↥(F.map (MulAut.conj t).toMonoidHom) = 16 :=
    fun t => (Subgroup.card_map_of_injective (MulAut.conj t).injective).trans hcardF
  obtain ⟨W₁, hW₁, himg₁⟩ := exists_radical_image g hR hVA hginj hX₁ (hel s) (hcard s)
  obtain ⟨W₂, hW₂, himg₂⟩ := exists_radical_image g hR hVA hginj hX₂ (hel (s * r₃))
    (hcard (s * r₃))
  have h12 : W₁ ≠ W₂ := by
    intro h
    obtain ⟨f, hf, hfn⟩ := hr3F
    have e1 : s⁻¹ * (s * f * s⁻¹) * s = f := by group
    have h1 : s * f * s⁻¹ ∈ F.map (MulAut.conj s).toMonoidHom :=
      mem_conjSub.2 (by rw [e1]; exact hf)
    rw [← himg₁, h, himg₂] at h1
    have h2 := mem_conjSub.1 h1
    have e : (s * r₃)⁻¹ * (s * f * s⁻¹) * (s * r₃) = r₃⁻¹ * f * r₃ := by group
    rw [e, hr3i] at h2
    rw [hr3i] at hfn
    exact hfn h2
  have hcases : W = W₁ ∨ W = W₂ := by
    rcases hW with rfl | rfl <;> rcases hW₁ with rfl | rfl <;> rcases hW₂ with rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl h12
  have hmk : ∀ r₀ : Equiv.Perm (Fin 42), r₀ ∈ R → (∀ y, y ∈ (W.subgroupOf
      (normalizer (A : Set G))).map g ↔ r₀⁻¹ * y * r₀ ∈ F) → Nonempty (RadicalIdent A W) := by
    intro r₀ hr₀ himg'
    exact ⟨{ F := F, hF := hF, g := g, r₀ := r₀, r₀_mem := hr₀, g_mem := hgR, g_ker := hker
             W_le := hWV.1.trans hVA
             W_comm := fun w hw w' hw' => L34.comm_of_isElemAbelian hWV.2.1 hw hw'
             g_inj := fun n n' hn hn' h => hginj n n' (hWV.1 hn) (hWV.1 hn') h
             img := himg', F_cent := hFcent, F_comm := hFcomm }⟩
  rcases hcases with rfl | rfl
  · refine hmk s (S_le_R hsS) fun y => ?_
    rw [himg₁]
    exact mem_conjSub
  · refine hmk (s * r₃) (R.mul_mem (S_le_R hsS) r₃_mem_R) fun y => ?_
    rw [himg₂]
    exact mem_conjSub


end CFSG.OddStandard.Seitz77.V1Act

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification CFSG.PSL3Four
  CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem centralizer_V₁_le {G : Type*} [Group G] [Finite G]
    {A V V₁ V₂ W : Subgroup G} (hA : commutator ↥A = ⊤) (hZ : Odd (Nat.card (center ↥A)))
    (e : ↥A ⧸ center ↥A ≃* ↥PSL3Four.S) (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) (hsyl : l34SylCheck (enumBFS 42 gensS 20160).tabs = true)
    (hcheck : Certificates.Seitz77L34.l34FCentCheck (enumBFS 42 gTabs 241920).tabs = true) :
    normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ W ⊔ centralizer (A : Set G) := by
  obtain ⟨I⟩ := V1Act.exists_radicalIdent hA hZ e hV hR hW hsyl hcheck
  exact I.centralizer_le

theorem card_fixed_le_four {G : Type*} [Group G] [Finite G]
    {A V V₁ V₂ W : Subgroup G} (hA : commutator ↥A = ⊤) (hZ : Odd (Nat.card (center ↥A)))
    (e : ↥A ⧸ center ↥A ≃* ↥PSL3Four.S) (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) (hsyl : l34SylCheck (enumBFS 42 gensS 20160).tabs = true)
    (hcheck : Certificates.Seitz77L34.l34FCentCheck (enumBFS 42 gTabs 241920).tabs = true)
    (hact : Certificates.Seitz77L34.l34V1ActCheck (enumBFS 42 gTabs 241920).tabs = true) :
    ∀ x ∈ normalizer (A : Set G) ⊓ normalizer (W : Set G), x ∉ W ⊔ centralizer (A : Set G) →
      Nat.card ↥(W ⊓ centralizer ({x} : Set G)) ≤ 4 := by
  obtain ⟨I⟩ := V1Act.exists_radicalIdent hA hZ e hV hR hW hsyl hcheck
  obtain ⟨hcard, -⟩ := V1Act.l34V1ActCheck_spec I.hF enumerates_R hact
  exact fun x hx hxout => I.card_fixed_le_four hcard hx.1 hx.2 hxout

theorem relIndex_le_four {G : Type*} [Group G] [Finite G]
    {A V V₁ V₂ W : Subgroup G} (hA : commutator ↥A = ⊤) (hZ : Odd (Nat.card (center ↥A)))
    (e : ↥A ⧸ center ↥A ≃* ↥PSL3Four.S) (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) (hsyl : l34SylCheck (enumBFS 42 gensS 20160).tabs = true)
    (hcheck : Certificates.Seitz77L34.l34FCentCheck (enumBFS 42 gTabs 241920).tabs = true)
    (hact : Certificates.Seitz77L34.l34V1ActCheck (enumBFS 42 gTabs 241920).tabs = true) :
    ∀ E : Subgroup G, E ≤ normalizer (A : Set G) ⊓ normalizer (W : Set G) →
      (∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ centralizer (W : Set G) ∧ x * x ∈ centralizer (W : Set G)) →
      (centralizer (W : Set G)).relIndex E ≤ 4 := by
  obtain ⟨I⟩ := V1Act.exists_radicalIdent hA hZ e hV hR hW hsyl hcheck
  obtain ⟨-, hT⟩ := V1Act.l34V1ActCheck_spec I.hF enumerates_R hact
  exact fun E hE h => I.relIndex_le_four hT hE h

end CFSG.OddStandard.Seitz77
