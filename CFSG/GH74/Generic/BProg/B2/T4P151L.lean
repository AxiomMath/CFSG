module

public import CFSG.GH74.Generic.BProg.B2.T4P151G
public import CFSG.GH74.Generic.S1.TQ3BarMain

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.P151L

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup
open CFSG.GH74.Generic.BProg.B2.T4.P151G

@[expose] def PumpGen3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X → pPrimeCore 2 X = ⊥ →
    ∀ σ : X, orderOf σ = 2 → ∀ J : Subgroup X, IsCompIn (centralizer ({σ} : Set X)) J →
      P151Model.IsL3OddSD (↥J ⧸ center ↥J) → (∀ z ∈ J, (∀ l ∈ J, z * l = l * z) → z * z = 1 → z = 1) →
    ∀ L : Subgroup X, IsComponent L → GHList (↥L ⧸ center ↥L) →
      J ≤ L ⊔ L.map (MulAut.conj σ).toMonoidHom →
    ∀ e₁ e₂ : X, e₁ ∈ J → e₂ ∈ J → e₁ * e₁ = 1 → e₂ * e₂ = 1 → e₁ * e₂ = e₂ * e₁ →
      e₁ ≠ 1 → e₂ ≠ 1 → e₁ ≠ e₂ →
      L ≤ (L ⊓ centralizer ({e₁} : Set X)) ⊔ (L ⊓ centralizer ({e₂} : Set X)) ⊔
        (L ⊓ centralizer ({e₁ * e₂} : Set X))

section TwoQuot

variable {I : Type} [Group I]

theorem exists_hom_quot {Q : Type} [Group Q] [Finite Q] (f : I →* Q) (hf : Function.Surjective f)
    (N : Subgroup I) [N.Normal] (hN : Odd (Nat.card N)) (hle : f.ker ≤ N) (hq : IsQuasisimple Q) :
    ∃ h : Q →* I ⧸ N, Function.Surjective h ∧ h.ker ≤ center Q ∧ Odd (Nat.card h.ker) ∧
      ∀ i : I, h (f i) = (QuotientGroup.mk i : I ⧸ N) := by
  set e := QuotientGroup.quotientKerEquivOfSurjective f hf with he
  set m : I ⧸ f.ker →* I ⧸ N := QuotientGroup.map f.ker N (MonoidHom.id I) (fun x hx => hle hx) with hm
  set h : Q →* I ⧸ N := m.comp e.symm.toMonoidHom with hh
  have hfi : ∀ i : I, h (f i) = (QuotientGroup.mk i : I ⧸ N) := by
    intro i
    have h1 : e.symm (f i) = (QuotientGroup.mk i : I ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show m (e.symm (f i)) = _
    rw [h1]
    rfl
  have hs : Function.Surjective h := by
    intro y
    obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨f i, hfi i⟩
  have hker : h.ker ≤ N.map f := by
    intro q hq'
    obtain ⟨i, rfl⟩ := hf q
    have h1 : (QuotientGroup.mk i : I ⧸ N) = 1 := by rw [← hfi i]; exact hq'
    exact ⟨i, (QuotientGroup.eq_one_iff i).1 h1, rfl⟩
  have hodd : Odd (Nat.card h.ker) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hN (Subgroup.card_map_dvd N f)) (Subgroup.card_dvd_of_le hker)
  exact ⟨h, hs, Prop31.normal_le_center_of_odd hq inferInstance hodd, hodd, hfi⟩

theorem odd_card_sup_ker {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] (f₁ : I →* Q₁) (f₂ : I →* Q₂)
    (ho₁ : Odd (Nat.card f₁.ker)) (ho₂ : Odd (Nat.card f₂.ker)) : Odd (Nat.card ↥(f₁.ker ⊔ f₂.ker)) := by
  have hN : f₂.ker ≤ normalizer (f₁.ker : Set I) := fun x _ =>
    Subgroup.mem_normalizer_iff.2 fun n => ⟨fun hn => (f₁.normal_ker).conj_mem n hn x, fun hn => by
      have := (f₁.normal_ker).conj_mem _ hn x⁻¹
      simpa [mul_assoc] using this⟩
  have hc := card_sup_mul_card_inf₀ hN
  have hdvd : Nat.card ↥(f₁.ker ⊔ f₂.ker) ∣ Nat.card f₁.ker * Nat.card f₂.ker := ⟨_, hc.symm⟩
  exact Odd.of_dvd_nat (ho₁.mul ho₂) hdvd

theorem nonempty_centerQuot_equiv {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] [Finite Q₁] [Finite Q₂]
    (f₁ : I →* Q₁) (hf₁ : Function.Surjective f₁) (f₂ : I →* Q₂) (hf₂ : Function.Surjective f₂)
    (ho₁ : Odd (Nat.card f₁.ker)) (ho₂ : Odd (Nat.card f₂.ker)) (hq₁ : IsQuasisimple Q₁) (hq₂ : IsQuasisimple Q₂) :
    Nonempty (Q₁ ⧸ center Q₁ ≃* Q₂ ⧸ center Q₂) ∧
      ((∀ z : Q₁, z ∈ center Q₁ → z * z = 1 → z = 1) → ∀ z : Q₂, z ∈ center Q₂ → z * z = 1 → z = 1) := by
  set N : Subgroup I := f₁.ker ⊔ f₂.ker with hNdef
  have hNn : N.Normal := inferInstance
  have hNo : Odd (Nat.card N) := odd_card_sup_ker f₁ f₂ ho₁ ho₂
  obtain ⟨h₁, hs₁, hk₁, hko₁, hf₁i⟩ := exists_hom_quot f₁ hf₁ N hNo le_sup_left hq₁
  obtain ⟨h₂, hs₂, hk₂, hko₂, hf₂i⟩ := exists_hom_quot f₂ hf₂ N hNo le_sup_right hq₂
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hq₁ h₁ hs₁ hk₁
  obtain ⟨e₂⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hq₂ h₂ hs₂ hk₂
  refine ⟨⟨e₁.trans e₂.symm⟩, fun hZ₁ z hz hzz => ?_⟩
  have hwc : h₂ z ∈ center (I ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨q, rfl⟩ := hs₂ y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz q)]
  obtain ⟨y, hy⟩ := hs₁ (h₂ z)
  have hyc : y ∈ center Q₁ := by
    have := CFSG.LocalCores.comap_center_eq_of_perfect hq₁.1 h₁ hs₁ hk₁
    rw [← this]
    show h₁ y ∈ center (I ⧸ N)
    rw [hy]
    exact hwc
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  obtain ⟨j, rfl⟩ := hm
  set y' := y ^ (2 * j + 1) with hy'
  have hy'c : y' ∈ center Q₁ := Subgroup.pow_mem _ hyc _
  have hy'2 : y' ^ (2 ^ k) = 1 := by
    rw [hy', ← pow_mul, Nat.mul_comm (2 * j + 1) (2 ^ k), ← hkm, pow_orderOf_eq_one]
  have hzodd : z ^ (2 * j + 1) = z := by
    rw [pow_succ, pow_mul, sq, hzz, one_pow, one_mul]
  have hhy' : h₁ y' = h₂ z := by
    rw [hy', map_pow, hy, ← map_pow, hzodd]
  have hy'1 : y' = 1 := by
    by_contra hne
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hy'2)
    have hi0 : i ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hio
      exact hne (orderOf_eq_one_iff.1 hio)
    set t := y' ^ (2 ^ (i - 1)) with ht
    have ht2 : orderOf t = 2 := by
      have hdvd : 2 ^ (i - 1) ∣ orderOf y' := by rw [hio]; exact pow_dvd_pow 2 (Nat.sub_le i 1)
      rw [ht, orderOf_pow_of_dvd (by positivity) hdvd, hio, Nat.pow_div (Nat.sub_le i 1) (by norm_num)]
      have : i - (i - 1) = 1 := by omega
      rw [this, pow_one]
    have htc : t ∈ center Q₁ := Subgroup.pow_mem _ hy'c _
    have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
    have := hZ₁ t htc htt
    rw [this, orderOf_one] at ht2
    omega
  have hz1 : h₂ z = 1 := by rw [← hhy', hy'1, map_one]
  have hzk : z ∈ h₂.ker := hz1
  have hdvd : orderOf (⟨z, hzk⟩ : ↥h₂.ker) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [sq]; exact Subtype.ext hzz)
  have hdvd' : orderOf (⟨z, hzk⟩ : ↥h₂.ker) ∣ Nat.card h₂.ker := orderOf_dvd_natCard _
  have h1 : orderOf (⟨z, hzk⟩ : ↥h₂.ker) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hdvd'
      exact absurd (Odd.of_dvd_nat hko₂ hdvd') (by decide)
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)

end TwoQuot

section Group

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_of_barSub_le {M : Subgroup G} {a : G} (hO : pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≤ M)
    {L : Subgroup G} (hLC : L ≤ centralizer ({a} : Set G)) (h : S45.barSub a L ≤ S45.barSub a M) : L ≤ M := by
  intro l hl
  have hlC := hLC hl
  obtain ⟨m, hmC, hmM, hm⟩ := S45.mem_barSub.1 (h (S45.proj_mem_barSub hlC hl))
  have h1 : (⟨m, hmC⟩ : ↥(centralizer ({a} : Set G)))⁻¹ * ⟨l, hlC⟩ ∈
      pPrimeCore 2 ↥(centralizer ({a} : Set G)) := QuotientGroup.eq.1 hm
  have h2 : m⁻¹ * l ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G)) := ⟨_, h1, rfl⟩
  have e : l = m * (m⁻¹ * l) := by group
  rw [e]
  exact M.mul_mem hmM (hO h2)

theorem centralizer_proj_le {M : Subgroup G} {a u : G} (hu : u ∈ centralizer ({a} : Set G)) (huu : u * u = 1)
    (hM : centralizer ({a * u} : Set G) ≤ M) :
    centralizer ({proj a ⟨u, hu⟩} : Set (CentralizerBar a)) ≤ S45.barSub a M := by
  intro z hz
  have hu2 : (⟨u, hu⟩ : ↥(centralizer ({a} : Set G))) * ⟨u, hu⟩ = 1 := Subtype.ext huu
  obtain ⟨g, hgu, hgz⟩ := proj_cent a hu2 z (Subgroup.mem_centralizer_singleton_iff.1 hz)
  refine S45.mem_barSub.2 ⟨g, g.2, hM ?_, hgz⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hga : (g : G) * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 g.2
  have hgu' : (g : G) * u = u * g := congrArg Subtype.val hgu
  calc (g : G) * (a * u) = (g * a) * u := by group
    _ = a * (g * u) := by rw [hga]; group
    _ = a * (u * g) := by rw [hgu']
    _ = a * u * g := by group

omit [Finite G] in
theorem ghList_centerQuot {C : Subgroup G} (hK : KGH G) (hC : C ≠ ⊤) {Y : Type} [Group Y] (π : ↥C →* Y)
    (hπ : Function.Surjective π) (L : Subgroup Y) (hq : IsQuasisimple ↥L) : GHList (↥L ⧸ center ↥L) := by
  let Kpre : Subgroup ↥C := L.comap π
  let H : Subgroup G := Kpre.map C.subtype
  have hHle : H ≤ C := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hH : H ≠ ⊤ := fun h => hC (top_le_iff.1 (h ▸ hHle))
  let e₁ : ↥Kpre ≃* ↥H := Kpre.equivMapOfInjective C.subtype C.subtype_injective
  let q : ↥Kpre →* ↥L := (π.comp Kpre.subtype).codRestrict L fun k => k.2
  have hq' : Function.Surjective q := by
    intro k
    obtain ⟨c, hc⟩ := hπ (k : Y)
    exact ⟨⟨c, show π c ∈ L by rw [hc]; exact k.2⟩, Subtype.ext hc⟩
  let f : ↥H →* ↥L ⧸ center ↥L := (QuotientGroup.mk' (center ↥L)).comp (q.comp e₁.symm.toMonoidHom)
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (hq'.comp e₁.symm.surjective)
  exact Generic.ghList_of_surjection hK hH f hf hq.2.1 hq.2.2

end Group

section Main


theorem layer151F_of_pumpGen3 (hB : B_B2_g4) (hP : PumpGen3) : Layer151F := by
  intro G _ _ x K A M P Q H hs h1 h3 hk1 hL5 a s₀ I₀ e₀₁ e₀₂ haA hax hF₀
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, I, e₁, e₂, hF, hT⟩ := exists_frame151 hB hs h1 h3 hk1 hL5 haA hF₀.a1 hax
  set C := centralizer ({a} : Set G) with hC
  obtain ⟨-, hAel, -, -⟩ := hs.src
  have hAC : A ≤ C := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2 (P151Model.ea_comm hAel hb haA)
  have hO : pPrimeCoreOf 2 C ≤ M := pPrimeCoreOf_le_of_inU0 (inU0_A hs) hAC
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have := hs.hyp.simple
    apply hF.a1
    have hz : a ∈ center G := Subgroup.mem_center_iff.2 fun g => by
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hb | ht
    · rw [hb] at hz
      exact Subgroup.mem_bot.1 hz
    · exfalso
      obtain ⟨u, v, huv⟩ := hs.hyp.nonab
      apply huv
      have hv : v ∈ center G := ht ▸ Subgroup.mem_top v
      exact (Subgroup.mem_center_iff.1 hv u)
  have hsC : s ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hF.sa
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hF.ss) hF.s1
  set σ : CentralizerBar a := proj a ⟨s, hsC⟩ with hσ
  have hσ2 : orderOf σ = 2 := TwoThin.orderOf_barMk (TwoThin.orderOf_mk_centralizer hsC hs2)
  have hσσ : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ2, sq] at this
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  have hGen : Gen4 (CentralizerBar a) := Gen4.quotient (pPrimeCore 2 ↥C) (Gen4.subgroup C hs.hyp.gen4)
  have hO1 : pPrimeCore 2 (CentralizerBar a) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hKC : IsKGroupNative (CentralizerBar a) :=
    CFSG.SectionRank.IsKGroupCat.quotient (isKGroupNative_of_kgh hs.hyp.kgh hCtop) (pPrimeCore 2 ↥C)
  set Ib := S45.barSub a I with hIb
  have hIC : I ≤ C := hF.Icomp.1.trans inf_le_right
  have hIcomp : IsCompIn (centralizer ({σ} : Set (CentralizerBar a))) Ib := by
    have hΛ := TwoThin.isTwoComponent_centralizer_mk hF.Icomp hsC
    have hΛC := TwoThin.le_centralizer_mk hF.Icomp.1 hsC
    have h2 := TwoThin.isTwoComponent_map_barMk (TwoThin.orderOf_mk_centralizer hsC hs2) hΛC hΛ
    have hle : Ib ≤ centralizer ({σ} : Set (CentralizerBar a)) := by
      have h3 := Subgroup.map_mono (f := TwoThin.barMk ↥C) hΛC
      rw [TwoThin.map_centralizer_barMk (TwoThin.orderOf_mk_centralizer hsC hs2)] at h3
      exact h3
    exact hB _ hGen hKC hO1 σ hσ2 Ib (TwoThin.isPCompIn_two_iff.2 ⟨hle, h2⟩)
  have hIbq : IsQuasisimple ↥Ib := Prop31.isQuasisimple_of_isCompIn hIcomp
  have hf₂ : ∀ i : ↥I, proj a (Subgroup.inclusion hIC i) ∈ Ib := fun i => S45.proj_mem_barSub (hIC i.2) i.2
  set f₂ : ↥I →* ↥Ib := ((proj a).comp (Subgroup.inclusion hIC)).codRestrict Ib hf₂ with hf₂def
  have hf₂s : Function.Surjective f₂ := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hg, hgI, rfl⟩ := S45.mem_barSub.1 hy
    exact ⟨⟨g, hgI⟩, rfl⟩
  have hf₂o : Odd (Nat.card f₂.ker) := by
    have hk : f₂.ker = ((proj a).comp (Subgroup.inclusion hIC)).ker := MonoidHom.ker_codRestrict _ _ _
    rw [hk]
    have h0 := B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hIC) (Subgroup.inclusion_injective hIC)
      (pPrimeCore 2 ↥C) (Nat.Coprime.odd_of_left CFSG.pPrimeCore_coprime_card)
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h0)
  obtain ⟨Qt, _, _, f₁, hf₁s, hf₁o, hQq, hQT, hQZ⟩ := hT
  obtain ⟨⟨eQ⟩, htr⟩ := nonempty_centerQuot_equiv f₁ hf₁s f₂ hf₂s hf₁o hf₂o hQq hIbq
  have hIbT : P151Model.IsL3OddSD (↥Ib ⧸ center ↥Ib) := P151Model.isL3OddSD_equiv eQ hQT
  have hIbZ : ∀ z ∈ Ib, (∀ l ∈ Ib, z * l = l * z) → z * z = 1 → z = 1 := by
    intro z hz hzc hzz
    have h0 := htr hQZ ⟨z, hz⟩ (Subgroup.mem_center_iff.2 fun l => Subtype.ext (hzc l l.2).symm)
      (Subtype.ext hzz)
    exact congrArg Subtype.val h0
  have he₁C : e₁ ∈ C := hIC hF.e₁I
  have he₂C : e₂ ∈ C := hIC hF.e₂I
  have he₁₂C : e₁ * e₂ ∈ C := C.mul_mem he₁C he₂C
  set ē₁ : CentralizerBar a := proj a ⟨e₁, he₁C⟩ with hē₁
  set ē₂ : CentralizerBar a := proj a ⟨e₂, he₂C⟩ with hē₂
  have hē₁₂d : proj a ⟨e₁ * e₂, he₁₂C⟩ = ē₁ * ē₂ := by
    rw [hē₁, hē₂, ← map_mul]
    rfl
  have hē₁I : ē₁ ∈ Ib := S45.proj_mem_barSub he₁C hF.e₁I
  have hē₂I : ē₂ ∈ Ib := S45.proj_mem_barSub he₂C hF.e₂I
  have hē₁₁ : ē₁ * ē₁ = 1 := by
    rw [hē₁, ← map_mul, show (⟨e₁, he₁C⟩ : ↥C) * ⟨e₁, he₁C⟩ = 1 from Subtype.ext hF.e₁e₁, map_one]
  have hē₂₂ : ē₂ * ē₂ = 1 := by
    rw [hē₂, ← map_mul, show (⟨e₂, he₂C⟩ : ↥C) * ⟨e₂, he₂C⟩ = 1 from Subtype.ext hF.e₂e₂, map_one]
  have hē₁₂ : ē₁ * ē₂ = ē₂ * ē₁ := by
    rw [hē₁, hē₂, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hF.e₁e₂
  have hē₁1 : ē₁ ≠ 1 := fun h => hF.e₁1 (S45.eq_one_of_proj_eq_one_of_sq he₁C h hF.e₁e₁)
  have hē₂1 : ē₂ ≠ 1 := fun h => hF.e₂1 (S45.eq_one_of_proj_eq_one_of_sq he₂C h hF.e₂e₂)
  have he₁₂sq : e₁ * e₂ * (e₁ * e₂) = 1 := by
    calc e₁ * e₂ * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ := by group
      _ = e₁ * (e₁ * e₂) * e₂ := by rw [hF.e₁e₂]
      _ = (e₁ * e₁) * (e₂ * e₂) := by group
      _ = 1 := by rw [hF.e₁e₁, hF.e₂e₂, one_mul]
  have hē₁ne : ē₁ ≠ ē₂ := by
    intro h
    have h12 : proj a ⟨e₁ * e₂, he₁₂C⟩ = 1 := by rw [hē₁₂d, ← h, hē₁₁]
    have h0 := S45.eq_one_of_proj_eq_one_of_sq he₁₂C h12 he₁₂sq
    apply hF.e₁₂
    calc e₁ = e₁ * (e₁ * e₂) := by rw [h0, mul_one]
      _ = e₂ := by rw [← mul_assoc, hF.e₁e₁, one_mul]
  have hCē₁ : centralizer ({ē₁} : Set (CentralizerBar a)) ≤ S45.barSub a M :=
    centralizer_proj_le he₁C hF.e₁e₁ hF.Ce₁
  have hCē₂ : centralizer ({ē₂} : Set (CentralizerBar a)) ≤ S45.barSub a M :=
    centralizer_proj_le he₂C hF.e₂e₂ hF.Ce₂
  have hCē₁₂ : centralizer ({ē₁ * ē₂} : Set (CentralizerBar a)) ≤ S45.barSub a M := by
    rw [← hē₁₂d]
    exact centralizer_proj_le he₁₂C he₁₂sq hF.Ce₁₂
  obtain ⟨L₀, hL₀, hcase⟩ := S1.pumpup_dichotomy hs2 hsC hF.Icomp
  set L₀' : Subgroup (CentralizerBar a) := L₀.map (MulAut.conj σ⁻¹).toMonoidHom with hL₀'
  have hL₀'c : IsComponent L₀' := CFSG.LocalAnalysis.ComponentInitial.isComponent_conjSub hL₀ σ⁻¹
  have hIL : Ib ≤ L₀ ⊔ L₀' := by
    rcases hcase with ⟨-, h⟩ | ⟨-, hAB, h⟩
    · exact h.trans le_sup_left
    · refine h.trans ?_
      rintro _ ⟨y, rfl⟩
      exact CFSG.LocalAnalysis.ComponentInitial.swapDiag_mem_sup hAB y
  have hconj : ∀ Lb : Subgroup (CentralizerBar a),
      (Lb.map (MulAut.conj σ⁻¹).toMonoidHom).map (MulAut.conj σ).toMonoidHom = Lb := by
    intro Lb
    rw [Subgroup.map_map]
    have hid : (MulAut.conj σ).toMonoidHom.comp (MulAut.conj σ⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext g
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  have hL₀map : L₀.map (MulAut.conj σ).toMonoidHom = L₀' := by
    rw [hL₀', hσinv]
  have hcomp : ∀ Lb : Subgroup (CentralizerBar a), IsComponent Lb → Lb ≤ S45.barSub a M := by
    intro Lb hLb
    by_cases h0 : Lb = L₀ ∨ Lb = L₀'
    · have hJL : Ib ≤ Lb ⊔ Lb.map (MulAut.conj σ).toMonoidHom := by
        rcases h0 with rfl | rfl
        · rw [hL₀map]
          exact hIL
        · rw [hL₀', hconj L₀, sup_comm]
          exact hIL
      have hGH : GHList (↥Lb ⧸ center ↥Lb) :=
        ghList_centerQuot hs.hyp.kgh hCtop (proj a) (QuotientGroup.mk'_surjective _) Lb hLb.1
      have hgen := hP (CentralizerBar a) hGen hO1 σ hσ2 Ib hIcomp hIbT hIbZ Lb hLb hGH hJL ē₁ ē₂ hē₁I hē₂I
        hē₁₁ hē₂₂ hē₁₂ hē₁1 hē₂1 hē₁ne
      refine hgen.trans (sup_le (sup_le ?_ ?_) ?_)
      · exact inf_le_right.trans hCē₁
      · exact inf_le_right.trans hCē₂
      · exact inf_le_right.trans hCē₁₂
    · push Not at h0
      have hc₀ : ⁅L₀, Lb⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hL₀ hLb).resolve_left fun h => h0.1 h.symm
      have hc₁ : ⁅L₀', Lb⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hL₀'c hLb).resolve_left fun h => h0.2 h.symm
      have hsupc : L₀ ⊔ L₀' ≤ centralizer (Lb : Set (CentralizerBar a)) :=
        sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc₀)
          (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc₁)
      have hē₁c : ē₁ ∈ centralizer (Lb : Set (CentralizerBar a)) := hsupc (hIL hē₁I)
      refine le_trans ?_ hCē₁
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hē₁c) l hl
  show sSup {L | IsPCompIn 2 C L} ≤ M
  refine sSup_le fun L hL => ?_
  exact le_of_barSub_le hO hL.1 (hcomp _ (C3.Layer1.PumpCalc.isComponent_bar hL))

end Main

end CFSG.GH74.Generic.BProg.B2.T4.P151L
